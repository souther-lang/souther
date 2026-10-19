package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
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

    /** A year before the years asked is not one the dates are put in. */
    @Test
    void aYearOutsideTheYearsAskedChoosesNone() {
        var early = statement(-1990, Rel.LE, year(0, 1, NOT_MOVED));

        assertNull(YearsAWayAllows.choose(List.of(early), A_MONTH_AND_A_DAY));
    }

    /** A move defined only at dates in the early years takes no date in the years asked. */
    @Test
    void aMoveThatIsNotDefinedWhereTheYearsAreAskedChoosesNone() {
        var early = new DateTranslation(0, LocalDate.MIN.toEpochDay(),
                LocalDate.of(1990, 1, 1).toEpochDay());
        var year = statement(0, Rel.GE, year(0, 1, early));

        assertNull(YearsAWayAllows.choose(List.of(year), A_MONTH_AND_A_DAY));
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
