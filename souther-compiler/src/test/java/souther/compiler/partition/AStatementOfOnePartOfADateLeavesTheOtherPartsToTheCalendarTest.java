package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What statements of the years of dates leave of their months and days is read in the years the
 * statements are held at together, and what statements of months and days leave of the years is
 * read at the months and days that are the same in every year, the calendar's ends included.
 */
class AStatementOfOnePartOfADateLeavesTheOtherPartsToTheCalendarTest {

    private static final DateTranslation NOT_MOVED = DateTranslation.none();

    private static final DatesThatStandInEveryYear.Part MONTH =
            new DatesThatStandInEveryYear.Part(TakenAs.DatePart.MONTH, NOT_MOVED);
    private static final DatesThatStandInEveryYear.Part DAY =
            new DatesThatStandInEveryYear.Part(TakenAs.DatePart.DAY, NOT_MOVED);

    private static YearsAWayAllows.Year year(int date, long weight, DateTranslation moved) {
        return new YearsAWayAllows.Year(date, ExactRatio.of(weight), moved);
    }

    private static YearsAWayAllows.Statement statement(long constant, Rel relation,
                                                       YearsAWayAllows.Year... years) {
        return new YearsAWayAllows.Statement(List.of(years), ExactRatio.of(constant), relation);
    }

    private static final List<List<DatesThatStandInEveryYear.Part>> A_MONTH_AND_A_DAY =
            List.of(List.of(MONTH, DAY));

    /**
     * {@code year >= 2025} and {@code year <= 2025}: each holds at many years and the two at one.
     * The month and day of that year are the ones a year of 2025's pattern gives, which has no
     * twenty-ninth of February, and still is every month and every day.
     */
    @Test
    void statementsThatHoldAtOneYearTogetherGiveTheMonthsAndDaysOfThatYear() {
        var atLeast = statement(-2025, Rel.GE, year(0, 1, NOT_MOVED));
        var atMost = statement(-2025, Rel.LE, year(0, 1, NOT_MOVED));

        assertNotNull(YearsAWayAllows.choose(List.of(atLeast), A_MONTH_AND_A_DAY));
        int[] together = YearsAWayAllows.choose(List.of(atLeast, atMost), A_MONTH_AND_A_DAY);
        assertEquals(2025, together[0]);

        List<List<ExactRatio>> given =
                MonthsAndDaysOfOneDate.inYear(List.of(MONTH, DAY), 2025, List.of());
        assertFalse(given.contains(List.of(ExactRatio.of(2), ExactRatio.of(29))));
        assertTrue(MonthsAndDaysOfOneDate.coversEveryValue(given, List.of(MONTH, DAY)));
    }

    /** Statements that hold at no year together leave the dates no year. */
    @Test
    void statementsThatHoldAtNoYearTogetherChooseNone() {
        var atLeast = statement(-2025, Rel.GE, year(0, 1, NOT_MOVED));
        var below = statement(-2025, Rel.LT, year(0, 1, NOT_MOVED));

        assertNull(YearsAWayAllows.choose(List.of(atLeast, below), A_MONTH_AND_A_DAY));
    }

    /**
     * A difference of two years held to sixty by a statement from above and one from below: the
     * years are sixty apart, and the pair of them gives every month and day of both dates.
     */
    @Test
    void aDifferenceHeldToOneNumberByTwoStatementsChoosesYearsThatFarApart() {
        var atLeast = statement(60, Rel.LE, year(0, -1, NOT_MOVED), year(1, 1, NOT_MOVED));
        var below = statement(61, Rel.GT, year(0, -1, NOT_MOVED), year(1, 1, NOT_MOVED));
        var both = List.of(List.of(MONTH, DAY), List.of(MONTH, DAY));

        int[] years = YearsAWayAllows.choose(List.of(atLeast, below), both);
        assertEquals(60, years[0] - years[1]);
    }

    /**
     * Five years of one date, each moved by a different number of days and weighed so that the
     * weights add past the greatest whole number the type holds and come back round to one. Each
     * year weighed alone is past it already, so no year is one the program can work the sum at,
     * whatever the sum comes to.
     */
    @Test
    void weightsThatAddPastTheTypeAreNotTakenForTheirRemainder() {
        long nearlyHalfTheTypesRange = (1L << 62) - 1;
        var five = statement(-1, Rel.GE,
                year(0, nearlyHalfTheTypesRange, NOT_MOVED),
                year(0, nearlyHalfTheTypesRange, NOT_MOVED.thenAddDays(1)),
                year(0, nearlyHalfTheTypesRange, NOT_MOVED.thenAddDays(2)),
                year(0, nearlyHalfTheTypesRange, NOT_MOVED.thenAddDays(3)),
                year(0, 5, NOT_MOVED.thenAddDays(4)));

        assertNull(YearsAWayAllows.choose(List.of(five), A_MONTH_AND_A_DAY));
    }

    /** A year held to be far from the years of the calendar's middle: the years are looked for
     *  where the statements put them, and not among a fixed few. */
    @Test
    void aYearFarFromTheMiddleOfTheCalendarIsChosenWhereTheStatementPutsIt() {
        var early = statement(-1990, Rel.LE, year(0, 1, NOT_MOVED));
        int[] years = YearsAWayAllows.choose(List.of(early), A_MONTH_AND_A_DAY);
        assertTrue(years != null && years[0] <= 1990);

        var apart = statement(1000, Rel.LE, year(0, -1, NOT_MOVED), year(1, 1, NOT_MOVED));
        int[] pair = YearsAWayAllows.choose(List.of(apart),
                List.of(List.of(MONTH, DAY), List.of(MONTH, DAY)));
        assertTrue(pair != null && pair[0] - pair[1] >= 1000);
    }

    /** The last year the calendar has is a year; the one after it is none. */
    @Test
    void theCalendarsLastYearIsChosenAndTheOneAfterItIsNot() {
        var last = statement(-999_999_999, Rel.GE, year(0, 1, NOT_MOVED));
        var after = statement(-1_000_000_000, Rel.GE, year(0, 1, NOT_MOVED));

        assertEquals(999_999_999, YearsAWayAllows.choose(List.of(last), A_MONTH_AND_A_DAY)[0]);
        assertNull(YearsAWayAllows.choose(List.of(after), A_MONTH_AND_A_DAY));
    }

    /**
     * {@code year(a) - year(b) == 60} with {@code year(b) == 5000}: the one solution is 5060 and
     * 5000, found whichever of the two dates is chosen first.
     */
    @Test
    void theYearsAreFoundWhicheverDateIsChosenFirst() {
        var both = List.of(List.of(MONTH, DAY), List.of(MONTH, DAY));
        var gap = statement(-60, Rel.EQ, year(0, 1, NOT_MOVED), year(1, -1, NOT_MOVED));
        var fixed = statement(-5000, Rel.EQ, year(1, 1, NOT_MOVED));
        assertArrayEquals(new int[] {5060, 5000}, YearsAWayAllows.choose(List.of(gap, fixed), both));

        var gapTurned = statement(-60, Rel.EQ, year(1, 1, NOT_MOVED), year(0, -1, NOT_MOVED));
        var fixedTurned = statement(-5000, Rel.EQ, year(0, 1, NOT_MOVED));
        assertArrayEquals(new int[] {5000, 5060},
                YearsAWayAllows.choose(List.of(gapTurned, fixedTurned), both));
    }

    /**
     * {@code 100019 * year(a) == 100003 * year(b)}: the years are whole numbers only at multiples
     * of 100003 and 100019, which a look at the years in a row from any one year does not meet.
     */
    @Test
    void yearsThatOnlyWeightsFarApartAllowAreFound() {
        var both = List.of(List.of(MONTH, DAY), List.of(MONTH, DAY));
        var apart = statement(0, Rel.EQ, year(0, 100_019, NOT_MOVED), year(1, -100_003, NOT_MOVED));

        int[] years = YearsAWayAllows.choose(List.of(apart), both);
        assertEquals(100_019L * years[0], 100_003L * years[1]);

        var never = statement(1, Rel.EQ, year(0, 4, NOT_MOVED), year(1, -2, NOT_MOVED));
        assertNull(YearsAWayAllows.choose(List.of(never), both));
    }

    /** A year is a number of its own: no month or day goes with it as one of them goes with the
     *  other, and asking for it as a part is refused. */
    @Test
    void theYearIsNotAPartThatGoesWithAMonthAndADay() {
        assertThrows(IllegalArgumentException.class,
                () -> new DatesThatStandInEveryYear.Part(TakenAs.DatePart.YEAR, NOT_MOVED));
    }

    /** A move defined only at dates in the early years takes no date in the years asked. */
    @Test
    void aMoveThatIsNotDefinedWhereTheYearsAreAskedChoosesNone() {
        var early = new DateTranslation(0, LocalDate.MIN.toEpochDay(),
                LocalDate.of(1990, 1, 1).toEpochDay());
        var year = statement(0, Rel.GE, year(0, 1, early));

        assertNull(YearsAWayAllows.choose(List.of(year), A_MONTH_AND_A_DAY));
    }

    /** The days a month has in every year alike: the thirty-first of January is one, the
     *  twenty-ninth of February is not. */
    @Test
    void everyDayThatEveryYearHasIsADateThatStandsInEveryYear() {
        assertEquals(365, DatesThatStandInEveryYear.of(List.of(), List.of()).size());
    }

    /** A date moved a day back is in the year before it on the first of January only, so that
     *  month and day is not the same in the year asked of the moved date. */
    @Test
    void aDateAShiftTakesToAnotherYearInSomeYearsIsNotTheSameInEveryYear() {
        int withNoShift = DatesThatStandInEveryYear.of(List.of(), List.of()).size();
        int shiftedBack = DatesThatStandInEveryYear.of(List.of(),
                List.of(DateTranslation.none().thenAddDays(-1))).size();
        assertEquals(withNoShift - 1, shiftedBack);
    }

    /**
     * The twenty-eighth of December, moved four days on, is the first of January in every year
     * of the cycle and a date past the calendar in its last, so it is not a month and day at
     * which the date stands in every year. The twenty-seventh of December is.
     */
    @Test
    void aMonthAndDayThatAMoveTakesPastTheCalendarsEndIsNotTheSameInEveryYear() {
        var day = new DatesThatStandInEveryYear.Part(TakenAs.DatePart.DAY,
                DateTranslation.none().thenAddDays(4));
        List<DatesThatStandInEveryYear.Origin> origins =
                DatesThatStandInEveryYear.of(List.of(day), List.of());

        assertTrue(origins.stream().anyMatch(each -> each.month() == 12 && each.day() == 27));
        assertFalse(origins.stream().anyMatch(each -> each.month() == 12 && each.day() == 28));
    }
}
