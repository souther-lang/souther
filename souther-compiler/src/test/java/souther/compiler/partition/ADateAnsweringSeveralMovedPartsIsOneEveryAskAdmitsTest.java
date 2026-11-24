package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Today;
import souther.compiler.semantics.TakenAs.DatePart;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A date answering several parts of itself, each taken after it was moved as its own ask says, is
 * one every ask admits, and there is one wherever any date is.
 *
 * <p>The searched-for date is looked for among a decade of days and compared with a walk over every
 * one of them, so what is held is both halves of what a writer of such a date owes: what it offers
 * answers every ask, and it offers nothing only where nothing does. The parts are the calendar's
 * own ({@code java.time}), and the moves and the days they are defined at are the ones a chain of
 * {@code Date.addDays} comes to ({@link DateTranslation#thenAddDays}).
 *
 * <p>Years, months and days are asked together and moved or not, since a group is one question
 * about one date whichever parts it is made of. A group with no year in it is walked over a cycle
 * of the calendar, and is compared with a walk over every day of that cycle.
 *
 * <p>What the cases were held to: each change below was made to the search, one at a time, and the
 * tests named are the ones that refused it. A change of the cases is checked against this list
 * again.
 *
 * <pre>
 *   a cut one day late                         whatIsOffered…, monthsAndDays…, and most written cases
 *   a move's first day not cut at              whatIsOffered…
 *   a cut on the last day walked left out      whatIsOffered…, aDayOfTheMonthIsCut…, the ends of the calendar
 *   a run's answer before a cut not carried    whatIsOffered…, monthsAndDays…, aDayOfTheMonthIsCut…
 *   a run's answer before the first cut turned whatIsOffered…, monthsAndDays…, aDayOfTheMonthIsCut…
 *   the last day of a moved range not walked   whatIsOffered…, aDayOfTheMonthIsCut…, the ends of the calendar
 *   a month taken to start on its second day   monthsAndDays…, thePartsOfTheLastDates…
 *   a year's run of one day refused            whatIsOffered…
 *   a year's run ending on the thirtieth       whatIsOffered…, thePartsOfTheFirstDates…
 *   the cycle always started in 2000           monthsAndDays…
 *   a cycle of three years                     monthsAndDays…, theCycleWalked…, aCombinationOnlyACentury…
 *   the last value of a month or day dropped   whatIsOffered…, monthsAndDays…, asksDefinedAtFewerDays…
 *   the first day walked not cut at            whatIsOffered… and the written moved-year cases
 * </pre>
 */
class ADateAnsweringSeveralMovedPartsIsOneEveryAskAdmitsTest {

    /**
     * The day every search here is asked on, in 2000 — a leap year that starts a cycle of the
     * calendar, which is what the cases were chosen around: what is told apart here is how one
     * cycle is walked from the start of the day's year, and not which day that is.
     */
    private static final Today ASKED_ON = new Today(LocalDate.of(2000, 1, 1));

    /** The days a walk covers. A year asked for stands within a few years of this, and a move
     *  takes a date by under two of them. */
    private static final long FIRST = LocalDate.of(1997, 1, 1).toEpochDay();
    private static final long LAST = LocalDate.of(2007, 12, 31).toEpochDay();
    private static final long REACH = 400;

    private static final LocalDate[] DATES = everyDayAround();

    private static LocalDate[] everyDayAround() {
        LocalDate[] dates = new LocalDate[(int) (LAST - FIRST + 1 + 2 * REACH)];
        for (int at = 0; at < dates.length; at++) {
            dates[at] = LocalDate.ofEpochDay(FIRST - REACH + at);
        }
        return dates;
    }

    private static int partOn(DatePart part, long day) {
        LocalDate date = DATES[(int) (day - (FIRST - REACH))];
        return switch (part) {
            case YEAR -> date.getYear();
            case MONTH -> date.getMonthValue();
            case DAY -> date.getDayOfMonth();
        };
    }

    /**
     * Asks put together so that the date they meet at is known beforehand, which the walk confirms
     * before the search is held against it.
     *
     * @param what what the case is made to tell apart
     * @param on   the day the walk finds: the only one in a decade, or the first of a cycle; null
     *             where it finds none
     * @param asks what is asked of one date
     */
    private record Case(String what, LocalDate on, List<TermRealizations.DatePartAsk> asks) {

        static Case of(String what, LocalDate on, TermRealizations.DatePartAsk... asks) {
            return new Case(what, on, List.of(asks));
        }
    }

    private static TermRealizations.DatePartAsk ask(DatePart part, DateTranslation moved,
                                                    int value) {
        return new TermRealizations.DatePartAsk(part, moved, new NumericSet.At(Count.of(value)));
    }

    private static TermRealizations.DatePartAsk awayFrom(DatePart part, DateTranslation moved,
                                                         int one, int other) {
        return new TermRealizations.DatePartAsk(part, moved,
                new NumericSet.AwayFrom(List.<Place>of(Count.of(one), Count.of(other))));
    }

    private static DateTranslation by(long days) {
        return DateTranslation.none().thenAddDays(days);
    }

    /** Moving nothing, and defined only from {@code first} to {@code last}. */
    private static DateTranslation between(LocalDate first, LocalDate last) {
        return new DateTranslation(0, first.toEpochDay(), last.toEpochDay());
    }

    private static boolean admits(TermRealizations.DatePartAsk ask, long day) {
        return ask.moved().definedAt(day)
                && ask.wanted().holds(Count.of(partOn(ask.part(), day + ask.moved().offsetDays())),
                        Carrier.WHOLE);
    }

    private static TermRealizations.DatePartAsk year(DateTranslation moved, int year) {
        return new TermRealizations.DatePartAsk(DatePart.YEAR, moved,
                new NumericSet.At(Count.of(year)));
    }

    /**
     * Whatever is offered answers every ask, and nothing is offered only where nothing does.
     *
     * <p>The search looks only at the days where some ask is answered otherwise than on the day
     * before, so what it can get wrong is where those days are: one too late, one too early, or
     * one left out. A date answered on many days hides that, since the day after a misplaced cut
     * answers as well. So each case here is answered on one day only, and that day is one the walk
     * reaches only by a cut of its own kind: the first day a narrow ask is defined at; the first
     * of a month reached by an ask a day back turning, and a day two moved months meet at, which
     * no unmoved ask cuts at, so the months of a moved date have to start where the calendar
     * starts them; the first and the last day of the year walked, and the first of a year walked
     * a month back; the last day of a year a second year ask moves into the next; a year walked
     * that is one day long; the day an ask leaving all but two months is answered again; and the
     * day an ask leaving all but two years stops being answered. Beside most of them stands one
     * that misses by a day and is answered nowhere, so an offer of a date that does not answer is
     * seen as well. That each case is answered on its day and no other is the walk's finding, and
     * is held before the search is.
     */
    @Test
    void whatIsOfferedAnswersEveryAskAndNothingIsOfferedOnlyWhereNothingDoes() {
        DateTranslation none = DateTranslation.none();
        LocalDate midsummer = LocalDate.of(2001, 6, 15);
        List<Case> cases = List.of(
                Case.of("the first day a narrow ask is defined at",
                        LocalDate.of(2001, 3, 31), year(none, 2001), ask(DatePart.MONTH,
                                between(LocalDate.of(2001, 3, 31), LocalDate.of(2001, 4, 30)), 3)),
                Case.of("a narrow ask defined from the day after", null, year(none, 2001),
                        ask(DatePart.MONTH,
                                between(LocalDate.of(2001, 4, 1), LocalDate.of(2001, 4, 30)), 3)),
                Case.of("the first of a month a day back turns at", LocalDate.of(2001, 5, 1),
                        year(none, 2001), ask(DatePart.MONTH, by(-1), 4),
                        ask(DatePart.MONTH, none, 5)),
                Case.of("a month a day back and a month after the next", null, year(none, 2001),
                        ask(DatePart.MONTH, by(-1), 4), ask(DatePart.MONTH, none, 6)),
                Case.of("the one day whose day before and the day before that are in two months",
                        LocalDate.of(2001, 5, 2), year(none, 2001),
                        ask(DatePart.MONTH, by(-1), 5), ask(DatePart.MONTH, by(-2), 4)),
                Case.of("the last day of the year walked", LocalDate.of(2001, 12, 31),
                        year(none, 2001), ask(DatePart.MONTH, none, 12),
                        ask(DatePart.DAY, none, 31)),
                Case.of("December a day on and the thirty-first", null, year(none, 2001),
                        ask(DatePart.MONTH, by(1), 12), ask(DatePart.DAY, none, 31)),
                Case.of("the first day of the year walked", LocalDate.of(2001, 1, 1),
                        year(none, 2001), ask(DatePart.MONTH, none, 1), ask(DatePart.DAY, none, 1)),
                Case.of("the first day of a year walked a month back", LocalDate.of(2001, 1, 31),
                        year(by(-30), 2001), ask(DatePart.MONTH, none, 1),
                        ask(DatePart.DAY, none, 31)),
                Case.of("the last day of a year whose next day is the next year",
                        LocalDate.of(2001, 12, 31), year(none, 2001), year(by(1), 2002)),
                Case.of("the next day in the next year, on the thirtieth", null,
                        year(none, 2001), year(by(1), 2002), ask(DatePart.DAY, none, 30)),
                Case.of("a year walked over one day", midsummer,
                        year(between(midsummer, midsummer), 2001)),
                Case.of("a year walked over one day of another year", null,
                        year(between(midsummer, midsummer), 2002)),
                Case.of("the first day after two months left out", LocalDate.of(2001, 4, 1),
                        year(none, 2001), awayFrom(DatePart.MONTH, none, 2, 3),
                        ask(DatePart.MONTH, by(-1), 3)),
                Case.of("the one day whose year before is neither of two left out",
                        LocalDate.of(2003, 1, 1), year(none, 2003),
                        awayFrom(DatePart.YEAR, by(-366), 2002, 2003)),
                Case.of("the first of March after a leap day", LocalDate.of(2004, 3, 1),
                        year(none, 2004), ask(DatePart.DAY, by(-1), 29),
                        ask(DatePart.MONTH, none, 3), ask(DatePart.DAY, none, 1)),
                Case.of("the first of March in a year with no leap day", null,
                        year(none, 2001), ask(DatePart.DAY, by(-1), 29),
                        ask(DatePart.MONTH, none, 3), ask(DatePart.DAY, none, 1)));
        int offered = 0;
        int refused = 0;
        for (Case each : cases) {
            List<TermRealizations.DatePartAsk> asks = each.asks();
            List<LocalDate> answering = new ArrayList<>();
            for (long day = FIRST; day <= LAST; day++) {
                final long on = day;
                if (asks.stream().allMatch(ask -> admits(ask, on))) {
                    answering.add(LocalDate.ofEpochDay(day));
                }
            }
            String where = each.what() + ": " + asks;
            assertEquals(each.on() == null ? List.of() : List.of(each.on()), answering,
                    "the days the walk finds, " + where);
            boolean somethingAnswers = !answering.isEmpty();

            TermRealizations.Search found =
                    TermRealizations.dateAnsweringMovedParts(asks, Carrier.DATE, ASKED_ON);

            if (somethingAnswers) {
                assertNotNull(found.on(),
                        "a date answers every ask, and none was offered: " + where);
            }
            if (found.on() == null) {
                assertTrue(found.everyOne(),
                        "nothing was offered by a walk that stopped: " + where);
                assertFalse(somethingAnswers, where);
                refused++;
            } else {
                long day = found.on().toEpochDay();
                assertTrue(asks.stream().allMatch(ask -> admits(ask, day)),
                        found.on() + " was offered and does not answer every ask: " + where);
                offered++;
            }
        }
        // So that a walk which offered nothing, or refused nothing, cannot pass for one that was
        // right every time.
        assertTrue(offered > 0, "no case had a date");
        assertTrue(refused > 0, "every case had a date");
    }

    /** The first day a walk of one cycle starts at, where the asks are defined there. */
    private static final long CYCLE_FROM = ASKED_ON.firstOfItsYear();

    /** The days of one Gregorian cycle, counted with {@code java.time}. */
    private static final long CYCLE =
            LocalDate.ofEpochDay(CYCLE_FROM).plusYears(400).toEpochDay() - CYCLE_FROM;

    /** The month and the day of every date from a little before the cycle to a little after it,
     *  so a walk over all of them reads an array rather than the calendar. */
    private static final long WIDE_FROM = CYCLE_FROM - 4 * REACH;
    private static final int[] MONTHS = new int[(int) (CYCLE + 8 * REACH)];
    private static final int[] DAYS = new int[MONTHS.length];

    static {
        for (int at = 0; at < MONTHS.length; at++) {
            LocalDate date = LocalDate.ofEpochDay(WIDE_FROM + at);
            MONTHS[at] = date.getMonthValue();
            DAYS[at] = date.getDayOfMonth();
        }
    }

    private static boolean admitsWide(TermRealizations.DatePartAsk ask, long day) {
        if (!ask.moved().definedAt(day)) {
            return false;
        }
        int at = (int) (day + ask.moved().offsetDays() - WIDE_FROM);
        int value = ask.part() == DatePart.MONTH ? MONTHS[at] : DAYS[at];
        return ask.wanted().holds(Count.of(value), Carrier.WHOLE);
    }

    /**
     * Months and days with no year among them are answered by a date every ask admits, and nothing
     * is offered only where no date does.
     *
     * <p>Held against a walk over every day of more than a cycle around where the search starts,
     * which covers every day the narrower moves here are defined at. The walk knows nothing of
     * where the search starts or stops, so neither the window it picks nor the cuts it makes can
     * leave a date out unseen.
     *
     * <p>What the search decides beyond where it cuts is which days it walks: from where every
     * ask is defined, over a cycle, a year at a time. The cases tell those choices apart. Asks
     * defined only before the year the cycle starts at, or only within part of a year inside it,
     * stand beside ones that miss by a day. A leap day a year's days on is first met three years
     * into the cycle, which a walk of fewer years does not reach. Each year walked starts its cuts
     * afresh, so a day answered only on the second day of a year, or where two moved months meet,
     * or where a month left out ends, is found only where each ask's runs start where the
     * calendar's do. The rest are what a month and a day of the month a day back or a month on
     * reach and do not, and a month a day back that January cannot have.
     */
    @Test
    void monthsAndDaysWithNoYearAreAnsweredWhereverADateAnswersThem() {
        DateTranslation none = DateTranslation.none();
        LocalDate july = LocalDate.of(2003, 7, 20);
        LocalDate august = LocalDate.of(2003, 8, 10);
        List<Case> cases = List.of(
                Case.of("a month asked only in a year before the cycle", LocalDate.of(1998, 5, 1),
                        ask(DatePart.MONTH,
                                between(LocalDate.of(1998, 1, 1), LocalDate.of(1998, 12, 31)), 5)),
                Case.of("a month asked only over days before the cycle that hold no such month",
                        null, ask(DatePart.MONTH,
                                between(LocalDate.of(1998, 6, 1), LocalDate.of(1999, 4, 30)), 5)),
                Case.of("the one twentieth a narrow ask inside the cycle is defined at", july,
                        ask(DatePart.MONTH, between(july.withDayOfMonth(1), august), 7),
                        ask(DatePart.DAY, none, 20)),
                Case.of("a narrow ask inside the cycle that stops the day before", null,
                        ask(DatePart.MONTH, between(july.withDayOfMonth(1), july.minusDays(1)),
                                7),
                        ask(DatePart.DAY, none, 20)),
                Case.of("a day whose day before and the day before that are in two months",
                        LocalDate.of(1997, 5, 2),
                        ask(DatePart.MONTH, by(-1), 5), ask(DatePart.MONTH, by(-2), 4)),
                Case.of("the day after a year walked starts", LocalDate.of(1997, 1, 2),
                        ask(DatePart.MONTH, none, 1), ask(DatePart.DAY, none, 2)),
                Case.of("a leap day", LocalDate.of(2000, 2, 29),
                        ask(DatePart.MONTH, none, 2), ask(DatePart.DAY, none, 29)),
                Case.of("a leap day a year's days on", LocalDate.of(1999, 3, 1),
                        ask(DatePart.MONTH, by(365), 2), ask(DatePart.DAY, by(365), 29)),
                Case.of("the first of a month after a thirty-first", LocalDate.of(1996, 11, 1),
                        ask(DatePart.DAY, by(-1), 31), ask(DatePart.DAY, none, 1)),
                Case.of("the first of March after a thirty-first", null,
                        ask(DatePart.DAY, by(-1), 31), ask(DatePart.MONTH, none, 3),
                        ask(DatePart.DAY, none, 1)),
                Case.of("a date in March a month on that is a thirty-first",
                        LocalDate.of(1997, 1, 31),
                        ask(DatePart.MONTH, by(30), 3), ask(DatePart.DAY, none, 31)),
                Case.of("the first day after two months left out", LocalDate.of(1997, 4, 1),
                        awayFrom(DatePart.MONTH, none, 2, 3), ask(DatePart.MONTH, by(-1), 3)),
                Case.of("January whose day before is neither December nor January", null,
                        awayFrom(DatePart.MONTH, by(-1), 1, 12), ask(DatePart.MONTH, none, 1)));
        int offered = 0;
        int refused = 0;
        for (Case each : cases) {
            List<TermRealizations.DatePartAsk> asks = each.asks();
            LocalDate first = null;
            for (long day = WIDE_FROM + REACH; day < WIDE_FROM + MONTHS.length - REACH
                    && first == null; day++) {
                final long on = day;
                if (asks.stream().allMatch(ask -> admitsWide(ask, on))) {
                    first = LocalDate.ofEpochDay(day);
                }
            }
            String where = each.what() + ": " + asks;
            assertEquals(each.on(), first, "the first day the walk finds, " + where);
            boolean somethingAnswers = first != null;

            TermRealizations.Search found =
                    TermRealizations.dateAnsweringMovedParts(asks, Carrier.DATE, ASKED_ON);

            assertTrue(found.everyOne(), "a cycle is every day there is to ask: " + where);
            assertEquals(somethingAnswers, found.on() != null, where);
            if (found.on() == null) {
                refused++;
            } else {
                long day = found.on().toEpochDay();
                assertTrue(asks.stream().allMatch(ask -> admitsWide(ask, day)),
                        found.on() + " was offered and does not answer every ask: " + where);
                offered++;
            }
        }
        assertTrue(offered > 0, "no case had a date");
        assertTrue(refused > 0, "every case had a date");
    }

    /**
     * A combination only a century that is no leap year makes is found, though no decade around the
     * start of the cycle has it.
     *
     * <p>Four years of days after the first of March are the first of March again where a leap day
     * falls between, and the second where none does: the years from 2096 to 2100 have none, since
     * 2100 is not a leap year.
     */
    @Test
    void aCombinationOnlyACenturyWithNoLeapDayMakesIsFound() {
        long fourYears = 4 * 365 + 1;
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(List.of(
                part(DatePart.MONTH, 3), part(DatePart.DAY, 1),
                new TermRealizations.DatePartAsk(DatePart.DAY,
                        DateTranslation.none().thenAddDays(fourYears),
                        new NumericSet.At(Count.of(2)))), Carrier.DATE, ASKED_ON);

        LocalDate first = null;
        for (LocalDate on = LocalDate.ofEpochDay(CYCLE_FROM); first == null;
                on = on.plusDays(1)) {
            if (on.getMonthValue() == 3 && on.getDayOfMonth() == 1
                    && on.plusDays(fourYears).getDayOfMonth() == 2) {
                first = on;
            }
        }
        assertEquals(LocalDate.of(2096, 3, 1), first);
        assertEquals(first, found.on());
        assertTrue(found.everyOne());
    }

    /**
     * The cycle walked is one every ask is defined throughout, and not one that starts where the
     * ask defined furthest back does.
     *
     * <p>The same combination, with the move four years on defined only from 2300: every first of
     * March from then on has a leap day within four years until 2500, which is not a leap year, so
     * the first date that answers is in 2496. A cycle starting in 2000 holds no day of it.
     */
    @Test
    void theCycleWalkedIsOneEveryAskIsDefinedThroughout() {
        long fourYears = 4 * 365 + 1;
        long from = LocalDate.of(2300, 1, 1).toEpochDay();
        DateTranslation late = new DateTranslation(fourYears, from,
                LocalDate.MAX.toEpochDay() - fourYears);
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(List.of(
                part(DatePart.MONTH, 3), part(DatePart.DAY, 1),
                new TermRealizations.DatePartAsk(DatePart.DAY, late,
                        new NumericSet.At(Count.of(2)))), Carrier.DATE, ASKED_ON);

        LocalDate first = null;
        for (LocalDate on = LocalDate.ofEpochDay(from); first == null; on = on.plusDays(1)) {
            if (on.getMonthValue() == 3 && on.getDayOfMonth() == 1
                    && on.plusDays(fourYears).getDayOfMonth() == 2) {
                first = on;
            }
        }
        assertEquals(LocalDate.of(2496, 3, 1), first);
        assertEquals(first, found.on());
        assertTrue(found.everyOne());
    }

    /** A month and a day no date has together are refused as the calendar's answer and not as a
     *  search that stopped. */
    @Test
    void aMonthAndADayNoDateHasAreRefusedAsTheCalendarsAnswer() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(List.of(
                new TermRealizations.DatePartAsk(DatePart.MONTH,
                        DateTranslation.none().thenAddDays(-1), new NumericSet.At(Count.of(2))),
                new TermRealizations.DatePartAsk(DatePart.DAY,
                        DateTranslation.none().thenAddDays(-1), new NumericSet.At(Count.of(30)))),
                Carrier.DATE, ASKED_ON);

        assertNull(found.on());
        assertTrue(found.everyOne());
    }

    /** The day before the first of March is the last of February, whichever year it is in. */
    @Test
    void theDayBeforeTheFirstOfMarchIsTheLastOfFebruary() {
        DateTranslation back = DateTranslation.none().thenAddDays(-1);
        TermRealizations.Search leap = TermRealizations.dateAnsweringMovedParts(List.of(
                new TermRealizations.DatePartAsk(DatePart.DAY, back,
                        new NumericSet.At(Count.of(29))),
                part(DatePart.MONTH, 3), part(DatePart.DAY, 1)), Carrier.DATE, ASKED_ON);
        TermRealizations.Search common = TermRealizations.dateAnsweringMovedParts(List.of(
                new TermRealizations.DatePartAsk(DatePart.DAY, back,
                        new NumericSet.At(Count.of(28))),
                part(DatePart.MONTH, 3), part(DatePart.DAY, 1)), Carrier.DATE, ASKED_ON);

        assertEquals(LocalDate.of(2000, 3, 1), leap.on());
        assertEquals(LocalDate.of(2001, 3, 1), common.on());
    }

    /**
     * Asks defined at fewer days than a cycle are walked over those days, wherever they are, and
     * asks defined only near the end of the calendar are walked there.
     */
    @Test
    void asksDefinedAtFewerDaysThanACycleAreWalkedOverThoseDays() {
        long from = LocalDate.of(5000, 1, 1).toEpochDay();
        DateTranslation narrow = new DateTranslation(1, from, from + 40);
        TermRealizations.Search inside = TermRealizations.dateAnsweringMovedParts(List.of(
                new TermRealizations.DatePartAsk(DatePart.DAY, narrow,
                        new NumericSet.At(Count.of(9)))), Carrier.DATE, ASKED_ON);
        TermRealizations.Search outside = TermRealizations.dateAnsweringMovedParts(List.of(
                new TermRealizations.DatePartAsk(DatePart.MONTH, narrow,
                        new NumericSet.At(Count.of(5)))), Carrier.DATE, ASKED_ON);

        assertEquals(LocalDate.of(5000, 1, 8), inside.on());
        assertNull(outside.on());
        assertTrue(outside.everyOne());

        DateTranslation late = DateTranslation.none().thenAddDays(
                LocalDate.MAX.toEpochDay() - LocalDate.of(2000, 1, 1).toEpochDay());
        TermRealizations.Search atTheEnd = TermRealizations.dateAnsweringMovedParts(List.of(
                new TermRealizations.DatePartAsk(DatePart.MONTH, late,
                        new NumericSet.At(Count.of(12)))), Carrier.DATE, ASKED_ON);

        assertNotNull(atTheEnd.on());
        assertEquals(12, atTheEnd.on().plusDays(late.offsetDays()).getMonthValue());
    }

    /**
     * A day of the month is cut where what its set leaves turns, and at no other day: a set that
     * leaves one day of the month cuts a month in at most three.
     *
     * <p>What a walk over a cycle costs is how many days it cuts at, so this is that cost held as
     * what the cuts are rather than as a time. Cut at every day, a cycle no date answers would be
     * walked a day at a time.
     */
    @Test
    void aDayOfTheMonthIsCutOnlyWhereWhatItsSetLeavesTurns() {
        DateTranslation back = DateTranslation.none().thenAddDays(-1);
        TermRealizations.PutToTheDays put = new TermRealizations.DatePartAsk(DatePart.DAY, back,
                new NumericSet.At(Count.of(30))).putToTheDays(Carrier.DATE);
        long from = LocalDate.of(2001, 1, 1).toEpochDay();
        long to = LocalDate.of(2001, 12, 31).toEpochDay();
        TreeSet<Long> cuts = new TreeSet<>();

        put.cutsInto(cuts, from, to);

        TreeSet<Long> expected = new TreeSet<>();
        for (long day = from + 1; day <= to; day++) {
            int moved = LocalDate.ofEpochDay(day - 1).getDayOfMonth();
            int before = LocalDate.ofEpochDay(day - 2).getDayOfMonth();
            if ((moved == 30) != (before == 30)) {
                expected.add(day);
            }
        }
        assertEquals(expected, cuts);
        assertTrue(cuts.size() <= 2 * 12, cuts.size() + " cuts in a year");
    }

    /** The year before a move is the one the date is in, and the one after it is the next day's. */
    @Test
    void theFirstDayOfAYearOnAMovedDateIsTheDayBeforeItsFirstOfJanuary() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(
                List.of(year(DateTranslation.none().thenAddDays(1), 2027)), Carrier.DATE,
                ASKED_ON);

        assertEquals(LocalDate.of(2026, 12, 31), found.on());
    }

    /** Two moves of one date answer two different years only at the first day of the later one. */
    @Test
    void aDateWhoseYearIsOneAndWhoseYesterdaysIsAnotherIsTheFirstOfJanuary() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(List.of(
                year(DateTranslation.none(), 2000),
                year(DateTranslation.none().thenAddDays(-1), 1999)), Carrier.DATE, ASKED_ON);

        assertEquals(LocalDate.of(2000, 1, 1), found.on());
    }

    /**
     * The year of a moved date and the month of the date itself are asked of one date, and neither
     * leaves the other unsolved.
     */
    @Test
    void aMovedYearAndAMonthOfTheDateItselfAreAskedTogether() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(List.of(
                year(DateTranslation.none().thenAddDays(-1), 2026),
                new TermRealizations.DatePartAsk(DatePart.MONTH, DateTranslation.none(),
                        new NumericSet.At(Count.of(1)))), Carrier.DATE, ASKED_ON);

        // Moved a day back it is in 2026, and it is in January: every date from the second of
        // January to the first of February answers both, and the first of them is offered.
        assertEquals(LocalDate.of(2026, 1, 2), found.on());
    }

    /** A day of the month asked beside a moved year is met at the day and not only at a cut. */
    @Test
    void aDayOfTheMonthAskedBesideAMovedYearIsMet() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(List.of(
                year(DateTranslation.none().thenAddDays(-1), 2026),
                new TermRealizations.DatePartAsk(DatePart.DAY, DateTranslation.none(),
                        new NumericSet.At(Count.of(17)))), Carrier.DATE, ASKED_ON);

        assertEquals(LocalDate.of(2026, 1, 17), found.on());
    }

    private static TermRealizations.DatePartAsk part(DatePart part, int value) {
        return new TermRealizations.DatePartAsk(part, DateTranslation.none(),
                new NumericSet.At(Count.of(value)));
    }

    /**
     * The ends of the calendar are dates like any other: asking for the part of a date in the last
     * month there is, or the first, does not step past what the calendar holds.
     */
    @Test
    void thePartsOfTheLastDatesAreAskedWithoutSteppingPastTheCalendar() {
        int last = LocalDate.MAX.getYear();
        DateTranslation back = DateTranslation.none().thenAddDays(-1);

        assertEquals(LocalDate.of(last, 12, 1), TermRealizations.dateAnsweringMovedParts(
                List.of(year(back, last), part(DatePart.MONTH, 12)), Carrier.DATE,
                ASKED_ON).on());
        assertEquals(LocalDate.of(last, 1, 31), TermRealizations.dateAnsweringMovedParts(
                List.of(year(back, last), part(DatePart.DAY, 31)), Carrier.DATE,
                ASKED_ON).on());
        assertEquals(LocalDate.MAX, TermRealizations.dateAnsweringMovedParts(
                List.of(year(back, last), part(DatePart.MONTH, 12), part(DatePart.DAY, 31)),
                Carrier.DATE, ASKED_ON).on());
    }

    @Test
    void thePartsOfTheFirstDatesAreAskedWithoutSteppingBeforeTheCalendar() {
        int first = LocalDate.MIN.getYear();
        DateTranslation on = DateTranslation.none().thenAddDays(1);

        assertEquals(LocalDate.MIN, TermRealizations.dateAnsweringMovedParts(
                List.of(year(on, first), part(DatePart.MONTH, 1)), Carrier.DATE,
                ASKED_ON).on());
        assertEquals(LocalDate.of(first, 1, 1), TermRealizations.dateAnsweringMovedParts(
                List.of(year(on, first), part(DatePart.DAY, 1)), Carrier.DATE,
                ASKED_ON).on());
        // Moved a day on, the last of December is in the next year: the thirtieth is the last day
        // of the first year there is that answers.
        assertEquals(LocalDate.of(first, 12, 30), TermRealizations.dateAnsweringMovedParts(
                List.of(year(on, first), part(DatePart.MONTH, 12), part(DatePart.DAY, 30)),
                Carrier.DATE, ASKED_ON).on());
    }

    /** A shift of centuries is as exact as one of a day. */
    @Test
    void aMoveOfCenturiesIsAsExactAsAMoveOfADay() {
        for (long days : new long[] {100_000, -100_000, 36_524_219, -36_524_219}) {
            TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(
                    List.of(year(DateTranslation.none().thenAddDays(days), 2010)),
                    Carrier.DATE, ASKED_ON);

            assertEquals(LocalDate.of(2010, 1, 1).minusDays(days), found.on(),
                    "moved by " + days);
        }
    }

    /** A leap year does not move the line: a move of 365 days is not a move of a year. */
    @Test
    void aMoveOfAYearsDaysAcrossALeapDayIsNotAMoveOfAYear() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(
                List.of(year(DateTranslation.none().thenAddDays(365), 2025)), Carrier.DATE,
                ASKED_ON);

        assertEquals(LocalDate.of(2024, 1, 2), found.on());
    }
}
