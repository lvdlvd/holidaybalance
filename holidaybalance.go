//
// Holidaybalance computes and updates employees vacation balance on google calendar.
//
// USAGE
//      go install github.com/lvdlvd/holidaybalance
//      # obtain a client_secret.json as per https://developers.google.com/google-apps/calendar/quickstart/go
//
//      holidaybalance [-n] user@yourdomain.ai
//
//  The -n flag supresses the updating of calendar entries.
//
//  The program iterates over the listed calendar for whole-day entries with
//  summary (title) containing the words "employee start date" and "{vacation|holiday} [half day]".
//
//  The program will query the public holiday calendar for Switzerland/Zürich. It caches a local copy.
//
//  Then it computes for each day the accrued and used holidays for that employee.
//  Vacation days accrue at a rate of 25 days per 365 days, that is one for every 14.6 calendar days.
//  2020-02-29 will be declared an extra public holiday. We'll see about 2024.
//
//  The descriptions of all "vacation" entries in the entire history will then be updated with
//  a final line Vacation from ...to... accrued/used/balance per the end date.
//
//  The program enforces no policies about allowed ranges of the balance, it is merely a tool to
//  keep an eye on them.
//
// PART TIME EMPLOYEES
//
//  The employee start date entry can have an optional description containing 'xxx %' to set a percentage
//  different from 100% (full time).
//
//  These entries may occur multiple times to change the FTE% over time.
//
//  When booking a vacation in a period with the FTE<100%, vacations with a span of more than
//  FTE% times a work week are counted as FTE days, not full days.  That is, if you work e.g 60%,
//  normally 3 days/week and you book 1, 2 or 3 calendar days, they are counted as 1,2 or 3 days but if you
//  book a 4 day or longer period, they are counted as 60% of those in /working/ days (that is, after discounting
//  public holidays).  The intention is that part-time employees can also just book 2 weeks of holiday.
//  If the results are wrong, book individual days instead.
//
//  The minimum granularity of a holiday you can take is half a day, which is discouraged anyway.
//  This facility is only so that people who work 2 mornings/week (20%) can take a day off.
//
// SECURITY AND LOGIN
//
//  In addition to this binary, you need the file client_secret.json in the same directory. This
//  provides access to the Google API's on behalf of the organisation.
//  See https://developers.google.com/google-apps/calendar/quickstart/go on how to go about that.
//
//  The first time the program is run by a user it will prompt with a URL to get user calendar modification
//  credentials. Use the calendar's owner account for those. They are stored in ~/.credentials/holidaybalance.json
//
//  If you have write access to other people's calendar you can update it for them.  They may not like that.
//
// KNOWN BUGS
//
//  Partial public holidays are counted as full days.
//  The program can not force people to take holidays or to properly record them.
//  If the public holiday calendar ever garbage-collects old entries, history will change.
//
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io/ioutil"
	"log"
	"os"
	"os/user"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"

	"golang.org/x/oauth2"
	"golang.org/x/oauth2/google"

	"github.com/pkg/errors"
	"google.golang.org/api/calendar/v3"
)

var (
	reStartDay = regexp.MustCompile(`(?i)employee\s+start\s+da(y|te)`)
	reVacation = regexp.MustCompile(`(?i)(holiday|vacation)`)
	reHalfDay  = regexp.MustCompile(`(?i)half\s+day`)
	rePercent  = regexp.MustCompile(`(\d\d|100)\s?%`)
)

const (
	// for every calendary year get 25 days of holiday. TODO make feb 29 an extra public holiday.
	HolidaysPerCalendarDay = 25. / 365.

	// source of public holidays
	holidayCalendar = "en.ch#holiday@group.v.calendar.google.com"

	// if the holiday event description contains the words 'holiday in', it should also contain this word.
	KANTON = "Zurich"
)

var noUpdate = flag.Bool("n", false, "don't update the calendar entries with new descriptions")

func main() {

	flag.Parse()

	if len(flag.Args()) != 1 {
		log.Fatalf("Usage: %s user@example.org", os.Args[0])
	}
	calName := flag.Arg(0)

	srv := getClient()

	cal, err := srv.CalendarList.Get(calName).Do()
	if err != nil {
		log.Fatalln(errors.Wrap(err, fmt.Sprintf("Failed to get events from %s", calName)))
	}
	log.Printf("Calendar %q id: %v", calName, cal.Id)

	hfile := filepath.Join(filepath.Dir(os.Args[0]), "publicholidays.json")
	holidays, err := loadPublicHolidays(hfile)
	if err != nil {
		log.Printf("Loading cached public holidays: %v", err)
		log.Printf("Updating cached public holidays...")
		holidays = getPublicHolidays(srv)
		storePublicHolidays(hfile, holidays)
	}
	log.Printf("Got %d public holidays", len(holidays))

	events := listAllDayEvents(srv, calName)
	if len(events) == 0 {
		log.Fatalf("No events from %q", calName)
	}
	endDate := events[0].Start
	for _, v := range events {
		if v.End.Date > endDate.Date {
			endDate = v.End
		}
	}
	log.Printf("Got %d all-day events, from %s to %s", len(events), events[0].Start.Date, endDate.Date)

	// build map date->workdays since first
	workdays := map[string]int{}
	n := 0
	for d, e := mustDate(events[0].Start), mustDate(endDate).Add(time.Hour); d.Before(e); d = d.AddDate(0, 0, 1) {
		dd := d.Format("2006-01-02")
		workdays[dd] = n
		if holidays[dd] == "" && d.Weekday() != time.Sunday && d.Weekday() != time.Saturday {
			n++
		}
	}

	var (
		// startDate is the start of the current employment period,
		// for example when an employee switched from 60% to 80%.
		startDate time.Time
		// lastDate is the end of the last processed event past the startDate.
		// It's used for computing accrued.
		lastDate *calendar.EventDateTime
		// lastVacationDate is the end of the last processed vacation event.
		lastVacationDate *calendar.EventDateTime
		// fte is the employment percent, 1 = 100%
		fte float64
		// accrued represents how much vacation is available.
		accrued float64
		// spent represent how much vacation has been used.
		spent float64
	)

	for _, ev := range events {
		if lastDate != nil {
			accrued += fte * HolidaysPerCalendarDay * float64(mustDate(ev.End).Sub(mustDate(lastDate))/(24*time.Hour))
			lastDate = ev.End
		}

		if reStartDay.MatchString(ev.Summary) {
			if startDate.IsZero() {
				// This is the very first day of employment.
				lastDate = ev.Start
			}

			startDate = mustDate(ev.Start)
			m := rePercent.FindStringSubmatch(ev.Summary)
			if m == nil {
				m = rePercent.FindStringSubmatch(ev.Description)
			}
			if m != nil {
				v, err := strconv.Atoi(m[1])
				if err == nil && v <= 100 {
					fte = float64(v) / 100
				}
			} else {
				fte = 1.0
			}
			log.Printf("Start date %v (%2.0f%%)", startDate.Format("2006-01-02"), fte*100)
			updateEvent(srv, cal.Id, ev, 0, 0, accrued, spent)
			continue
		}

		if reVacation.MatchString(ev.Summary) {
			if startDate.IsZero() {
				log.Fatal("no employee start date set. create a 1 day entry with summary 'Employee Start Date' and re-run this program.")
			}

			if lastDate.Date > ev.End.Date {
				log.Printf("vacation from %s to %s already accounted for", ev.Start.Date, ev.End.Date)
				continue
			}

			if lastVacationDate != nil && lastVacationDate.Date > ev.Start.Date {
				log.Printf("vacation from %s to %s partially accounted for up to %s", ev.Start.Date, ev.End.Date, lastVacationDate.Date)
				ev.Start = lastVacationDate // patch up
			}
			lastVacationDate = ev.End

			daysOff := float64(workdays[ev.End.Date] - workdays[ev.Start.Date])
			effDaysOff := daysOff
			// if the calendar period is longer than fte times a week, count as fte% days off only, not all
			calDays := float64(mustDate(ev.End).Sub(mustDate(ev.Start)) / (24 * time.Hour))
			if calDays >= 5*fte {
				effDaysOff = fte * daysOff
			} else if calDays < 1.01 && reHalfDay.MatchString(ev.Summary) {
				// TODO(lvd) maybe only do this if fte < 60%
				effDaysOff = .5
			}

			spent += effDaysOff

			updateEvent(srv, cal.Id, ev, daysOff, effDaysOff, accrued, spent)
		}
	}

	if lastVacationDate != nil {
		now := time.Now()
		y := mustDate(lastVacationDate).Year()
		eoy := time.Date(y+1, 1, 1, 0, 0, 0, 0, now.Location())
		accruedEoy := accrued + fte*HolidaysPerCalendarDay*float64(eoy.Sub(mustDate(lastVacationDate))/(24*time.Hour))
		fmt.Printf("vacation at %s: accrued %.1f, balance %.1f\n", eoy, accruedEoy, accruedEoy-spent)
	}
}

func updateEvent(srv *calendar.Service, calId string, ev *calendar.Event, daysOff, effDaysOff, accrued, spent float64) {
	balanceline := fmt.Sprintf("vacation from %s to %s: %.1f days (effective %.1f), accrued %.1f, spent %.1f balance %.1f",
		ev.Start.Date, ev.End.Date, daysOff, effDaysOff, accrued, spent, accrued-spent)
	fmt.Println(balanceline)

	if *noUpdate {
		return
	}

	lines := strings.Split(ev.Description, "\n")
	if len(lines) > 0 && strings.HasPrefix(lines[len(lines)-1], "vacation from ") {
		lines = lines[:len(lines)-1]
	}
	lines = append(lines, balanceline)
	newDescr := strings.Join(lines, "\n")

	if newDescr != ev.Description {
		if _, err := srv.Events.Patch(calId, ev.Id, &calendar.Event{Description: newDescr}).Do(); err != nil {
			log.Printf("Error updating event %q (%s): %v", ev.Summary, ev.Start.Date, err)
		} else {
			log.Printf("Updated event %q (%s)", ev.Summary, ev.Start.Date)
		}
	} else {
		log.Printf("No need to modify event %q (%s)", ev.Summary, ev.Start.Date)
	}
}

func listAllDayEvents(srv *calendar.Service, cal string) []*calendar.Event {
	var r []*calendar.Event
	tok := ""
	for {
		events, err := srv.Events.List(cal).ShowDeleted(false).PageToken(tok).Do()
		if err != nil {
			log.Fatalf("Listing %v: %v", cal, err)
		}

		for _, i := range events.Items {
			if i.Start == nil || i.End == nil {
				continue
			}

			// If the DateTime is an empty string the Event is an all-day Event and only Date is available.
			if i.Start.DateTime != "" {
				continue
			}
			if _, _, err := dateSpan(i); err != nil {
				log.Printf("invalid start/end date %q (%s) %v", i.Start.Date, i.Summary, err)
				continue
			}

			r = append(r, i)
		}

		tok = events.NextPageToken
		if tok == "" {
			break
		}
	}
	sort.Sort(byStartDate(r))
	return r
}

type byStartDate []*calendar.Event

func (b byStartDate) Len() int           { return len(b) }
func (b byStartDate) Swap(i, j int)      { b[i], b[j] = b[j], b[i] }
func (b byStartDate) Less(i, j int) bool { return b[i].Start.Date < b[j].Start.Date }

func mustDate(edt *calendar.EventDateTime) time.Time {
	d, err := time.Parse("2006-01-02", edt.Date)
	if err != nil {
		panic(err)
	}
	return d
}

func dateSpan(ev *calendar.Event) (b, e time.Time, err error) {
	b, err = time.Parse("2006-01-02", ev.Start.Date)
	if err != nil {
		return time.Time{}, time.Time{}, err
	}
	e, err = time.Parse("2006-01-02", ev.End.Date)
	if err != nil {
		return time.Time{}, time.Time{}, err
	}
	return b, e, nil
}

func loadPublicHolidays(path string) (map[string]string, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	r := map[string]string{}
	err = json.NewDecoder(f).Decode(&r)
	return r, err
}

func storePublicHolidays(path string, h map[string]string) {
	log.Printf("saving public holidays as %s", path)
	f, err := os.Create(path)
	if err != nil {
		log.Fatalf("Unable to write %s: %v", path, err)
	}
	defer f.Close()
	enc := json.NewEncoder(f)
	enc.SetIndent("", "\t")
	enc.Encode(h)
}

// Return sorted list of days with public holidays in Zürich.
func getPublicHolidays(srv *calendar.Service) map[string]string {
	r := map[string]string{}

	for _, ev := range listAllDayEvents(srv, holidayCalendar) {

		// if the description contains holiday in, it better contain Zurich too.
		if strings.Contains(ev.Description, "holiday in") && !strings.Contains(ev.Description, KANTON) {
			continue
		}

		b, e, err := dateSpan(ev)
		if err != nil {
			log.Printf("skipping %q: %v", ev.Summary, err)
			continue
		}

		for d := b; d.Before(e); d = d.AddDate(0, 0, 1) {
			r[d.Format("2006-01-02")] = ev.Summary
		}
		log.Printf("Public holiday: %s %d days: %s", ev.Start.Date, e.Sub(b)/(24*time.Hour), ev.Summary)
	}

	return r
}

func homeDir() string {
	usr, err := user.Current()
	if err != nil {
		log.Fatalln(err)
	}
	return usr.HomeDir
}

// getTokenFromWeb uses Config to request a Token.
// It returns the retrieved Token.
func tokenFromWeb(config *oauth2.Config) *oauth2.Token {
	authURL := config.AuthCodeURL("state-token", oauth2.AccessTypeOffline)
	log.Printf("Go to the following link in your browser then type the authorization code: \n%v\n", authURL)

	var code string
	if _, err := fmt.Scan(&code); err != nil {
		log.Fatalf("Unable to read authorization code %v", err)
	}

	tok, err := config.Exchange(oauth2.NoContext, code)
	if err != nil {
		log.Fatalf("Unable to retrieve token from web %v", err)
	}
	return tok
}

// tokenFromFile retrieves a Token from a given file path.
// It returns the retrieved Token and any read error encountered.
func loadToken(file string) (*oauth2.Token, error) {
	f, err := os.Open(file)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	t := &oauth2.Token{}
	err = json.NewDecoder(f).Decode(t)
	return t, err
}

// saveToken uses a file path to create a file and store the
// token in it.
func saveToken(file string, token *oauth2.Token) {
	log.Printf("Saving credential file to: %s\n", file)
	f, err := os.OpenFile(file, os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0600)
	if err != nil {
		log.Fatalf("Unable to cache oauth token: %v", err)
	}
	defer f.Close()
	json.NewEncoder(f).Encode(token)
}

// getClient uses a Context and Config to retrieve a Token
// then generate a Client. It returns the generated Client.
func getClient() *calendar.Service {

	home := homeDir()
	basename := filepath.Base(os.Args[0])

	cs, err := ioutil.ReadFile(filepath.Join(filepath.Dir(os.Args[0]), "client_secret.json"))
	if err != nil {
		cs, err = ioutil.ReadFile(filepath.Join(home, ".credentials", "client_secret.json"))
	}
	if err != nil {
		log.Fatalf("Unable to read client secret file: %v", err)
	}

	config, err := google.ConfigFromJSON(cs, calendar.CalendarScope)
	if err != nil {
		log.Fatalf("Unable to parse client secret file to config: %v", err)
	}

	tokenCacheDir := filepath.Join(home, ".credentials")
	cacheFile := filepath.Join(tokenCacheDir, basename+".json")
	tok, err := loadToken(cacheFile)
	if err != nil {
		os.MkdirAll(tokenCacheDir, 0700)
		tok = tokenFromWeb(config)
		saveToken(cacheFile, tok)
	}

	srv, err := calendar.New(config.Client(context.Background(), tok))
	if err != nil {
		log.Fatalf("Unable to construct calendar Client %v", err)
	}
	return srv
}
