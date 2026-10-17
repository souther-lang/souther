package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Place;
import souther.compiler.semantics.TakenAs.DatePart;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

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
 */
class ADateAnsweringSeveralMovedPartsIsOneEveryAskAdmitsTest {

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

    private static final List<DatePart> PARTS = List.of(DatePart.values());

    private static final long[] MOVES = {0, 1, -1, 30, -30, 365, -366};

    /** What a chain of moves is defined at, for the chains this walks: defined everywhere, or only
     *  between two days a step of the chain left. */
    private static DateTranslation chain(Random random) {
        long offset = MOVES[random.nextInt(MOVES.length)];
        DateTranslation whole = DateTranslation.none().thenAddDays(offset);
        if (random.nextInt(3) > 0) {
            return whole;
        }
        long from = LocalDate.of(1998 + random.nextInt(9), 1 + random.nextInt(12), 1)
                .toEpochDay();
        return new DateTranslation(offset, from, from + random.nextInt(900));
    }

    private static NumericSet numbers(Random random, DatePart part, boolean lead) {
        int range = switch (part) {
            case YEAR -> 5;
            case MONTH -> 12;
            case DAY -> 31;
        };
        int base = part == DatePart.YEAR ? 2000 : 1;
        Place value = Count.of(base + random.nextInt(range));
        return lead || random.nextBoolean() ? new NumericSet.At(value)
                : new NumericSet.AwayFrom(List.of(value, Count.of(base + random.nextInt(range))));
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
     */
    @Test
    void whatIsOfferedAnswersEveryAskAndNothingIsOfferedOnlyWhereNothingDoes() {
        Random random = new Random(2255);
        int offered = 0;
        int refused = 0;
        for (int round = 0; round < 600; round++) {
            List<TermRealizations.DatePartAsk> asks = new ArrayList<>();
            asks.add(new TermRealizations.DatePartAsk(DatePart.YEAR, chain(random),
                    numbers(random, DatePart.YEAR, true)));
            int more = random.nextInt(3);
            for (int each = 0; each < more; each++) {
                DatePart part = PARTS.get(random.nextInt(PARTS.size()));
                asks.add(new TermRealizations.DatePartAsk(part, chain(random),
                        numbers(random, part, false)));
            }

            TermRealizations.Search found =
                    TermRealizations.dateAnsweringMovedParts(asks, Carrier.DATE);

            boolean somethingAnswers = false;
            for (long day = FIRST; day <= LAST && !somethingAnswers; day++) {
                final long on = day;
                somethingAnswers = asks.stream().allMatch(ask -> admits(ask, on));
            }
            String where = asks.toString();
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
        assertTrue(offered > 50, "only " + offered + " rounds had a date");
        assertTrue(refused > 50, "only " + refused + " rounds had none");
    }

    /** The first day a walk of one cycle starts at, where the asks are defined there. */
    private static final long CYCLE_FROM = LocalDate.of(2000, 1, 1).toEpochDay();

    /** The days of one Gregorian cycle, counted with {@code java.time}. */
    private static final long CYCLE = LocalDate.of(2400, 1, 1).toEpochDay() - CYCLE_FROM;

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
     * Months and days with no year among them are answered by the first date of the cycle that
     * answers them, and nothing is offered only where no date of the cycle does.
     *
     * <p>The walk is held against every day of the cycle it says it walks, one by one: what it
     * offers is the first of them that every ask admits, so neither the cuts nor the years it is
     * walked in leave a date out.
     */
    @Test
    void monthsAndDaysWithNoYearAreAnsweredByTheFirstDateOfTheCycleThatAnswersThem() {
        Random random = new Random(2443);
        List<DatePart> noYear = List.of(DatePart.MONTH, DatePart.DAY);
        int offered = 0;
        int refused = 0;
        for (int round = 0; round < 300; round++) {
            List<TermRealizations.DatePartAsk> asks = new ArrayList<>();
            int many = 1 + random.nextInt(3);
            for (int each = 0; each < many; each++) {
                DatePart part = noYear.get(random.nextInt(noYear.size()));
                asks.add(new TermRealizations.DatePartAsk(part, chain(random),
                        numbers(random, part, random.nextBoolean())));
            }
            long first = asks.stream().mapToLong(each -> each.moved().first()).max()
                    .orElseThrow();
            long last = asks.stream().mapToLong(each -> each.moved().last()).min().orElseThrow();
            long from = Math.max(first, Math.min(CYCLE_FROM, last - CYCLE + 1));
            long to = Math.min(last, from + CYCLE - 1);
            LocalDate expected = null;
            for (long day = from; day <= to && expected == null; day++) {
                final long on = day;
                if (asks.stream().allMatch(ask -> admitsWide(ask, on))) {
                    expected = LocalDate.ofEpochDay(day);
                }
            }

            TermRealizations.Search found =
                    TermRealizations.dateAnsweringMovedParts(asks, Carrier.DATE);

            assertTrue(found.everyOne(), "a cycle is every day there is to ask: " + asks);
            assertEquals(expected, found.on(), asks.toString());
            if (expected == null) {
                refused++;
            } else {
                offered++;
            }
        }
        assertTrue(offered > 50, "only " + offered + " rounds had a date");
        assertTrue(refused > 20, "only " + refused + " rounds had none");
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
                        new NumericSet.At(Count.of(2)))), Carrier.DATE);

        LocalDate first = null;
        for (LocalDate on = LocalDate.of(2000, 1, 1); first == null; on = on.plusDays(1)) {
            if (on.getMonthValue() == 3 && on.getDayOfMonth() == 1
                    && on.plusDays(fourYears).getDayOfMonth() == 2) {
                first = on;
            }
        }
        assertEquals(LocalDate.of(2096, 3, 1), first);
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
                Carrier.DATE);

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
                part(DatePart.MONTH, 3), part(DatePart.DAY, 1)), Carrier.DATE);
        TermRealizations.Search common = TermRealizations.dateAnsweringMovedParts(List.of(
                new TermRealizations.DatePartAsk(DatePart.DAY, back,
                        new NumericSet.At(Count.of(28))),
                part(DatePart.MONTH, 3), part(DatePart.DAY, 1)), Carrier.DATE);

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
                        new NumericSet.At(Count.of(9)))), Carrier.DATE);
        TermRealizations.Search outside = TermRealizations.dateAnsweringMovedParts(List.of(
                new TermRealizations.DatePartAsk(DatePart.MONTH, narrow,
                        new NumericSet.At(Count.of(5)))), Carrier.DATE);

        assertEquals(LocalDate.of(5000, 1, 8), inside.on());
        assertNull(outside.on());
        assertTrue(outside.everyOne());

        DateTranslation late = DateTranslation.none().thenAddDays(
                LocalDate.MAX.toEpochDay() - LocalDate.of(2000, 1, 1).toEpochDay());
        TermRealizations.Search atTheEnd = TermRealizations.dateAnsweringMovedParts(List.of(
                new TermRealizations.DatePartAsk(DatePart.MONTH, late,
                        new NumericSet.At(Count.of(12)))), Carrier.DATE);

        assertNotNull(atTheEnd.on());
        assertEquals(12, atTheEnd.on().plusDays(late.offsetDays()).getMonthValue());
    }

    /** The year before a move is the one the date is in, and the one after it is the next day's. */
    @Test
    void theFirstDayOfAYearOnAMovedDateIsTheDayBeforeItsFirstOfJanuary() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(
                List.of(year(DateTranslation.none().thenAddDays(1), 2027)), Carrier.DATE);

        assertEquals(LocalDate.of(2026, 12, 31), found.on());
    }

    /** Two moves of one date answer two different years only at the first day of the later one. */
    @Test
    void aDateWhoseYearIsOneAndWhoseYesterdaysIsAnotherIsTheFirstOfJanuary() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(List.of(
                year(DateTranslation.none(), 2000),
                year(DateTranslation.none().thenAddDays(-1), 1999)), Carrier.DATE);

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
                        new NumericSet.At(Count.of(1)))), Carrier.DATE);

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
                        new NumericSet.At(Count.of(17)))), Carrier.DATE);

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
                List.of(year(back, last), part(DatePart.MONTH, 12)), Carrier.DATE).on());
        assertEquals(LocalDate.of(last, 1, 31), TermRealizations.dateAnsweringMovedParts(
                List.of(year(back, last), part(DatePart.DAY, 31)), Carrier.DATE).on());
        assertEquals(LocalDate.MAX, TermRealizations.dateAnsweringMovedParts(
                List.of(year(back, last), part(DatePart.MONTH, 12), part(DatePart.DAY, 31)),
                Carrier.DATE).on());
    }

    @Test
    void thePartsOfTheFirstDatesAreAskedWithoutSteppingBeforeTheCalendar() {
        int first = LocalDate.MIN.getYear();
        DateTranslation on = DateTranslation.none().thenAddDays(1);

        assertEquals(LocalDate.MIN, TermRealizations.dateAnsweringMovedParts(
                List.of(year(on, first), part(DatePart.MONTH, 1)), Carrier.DATE).on());
        assertEquals(LocalDate.of(first, 1, 1), TermRealizations.dateAnsweringMovedParts(
                List.of(year(on, first), part(DatePart.DAY, 1)), Carrier.DATE).on());
        // Moved a day on, the last of December is in the next year: the thirtieth is the last day
        // of the first year there is that answers.
        assertEquals(LocalDate.of(first, 12, 30), TermRealizations.dateAnsweringMovedParts(
                List.of(year(on, first), part(DatePart.MONTH, 12), part(DatePart.DAY, 30)),
                Carrier.DATE).on());
    }

    /** A shift of centuries is as exact as one of a day. */
    @Test
    void aMoveOfCenturiesIsAsExactAsAMoveOfADay() {
        for (long days : new long[] {100_000, -100_000, 36_524_219, -36_524_219}) {
            TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(
                    List.of(year(DateTranslation.none().thenAddDays(days), 2010)),
                    Carrier.DATE);

            assertEquals(LocalDate.of(2010, 1, 1).minusDays(days), found.on(),
                    "moved by " + days);
        }
    }

    /** A leap year does not move the line: a move of 365 days is not a move of a year. */
    @Test
    void aMoveOfAYearsDaysAcrossALeapDayIsNotAMoveOfAYear() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(
                List.of(year(DateTranslation.none().thenAddDays(365), 2025)), Carrier.DATE);

        assertEquals(LocalDate.of(2024, 1, 2), found.on());
    }
}
