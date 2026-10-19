package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A statement of the years of dates says nothing of their months and days where it holds at years
 * of every pattern of the calendar, and one of their months and days says nothing of the years
 * where a month and a day it lets through is the same in every year.
 */
class AStatementOfOnePartOfADateLeavesTheOtherPartsToTheCalendarTest {

    private static EveryPatternOfYears.Year year(int date, long weight, long offsetDays) {
        return new EveryPatternOfYears.Year(date, ExactRatio.of(weight), offsetDays);
    }

    /** {@code year(on) - year(birthday) >= 60}, written as {@code 60 + year(birthday) - year(on)
     *  <= 0}: far from the year it is held to, whichever leap years the two are. */
    @Test
    void aDifferenceOfYearsHeldToAHalfLineIsHeldAtEveryPattern() {
        List<EveryPatternOfYears.Year> difference = List.of(year(0, 1, 0), year(1, -1, -1));
        assertTrue(EveryPatternOfYears.heldBy(difference, 2, ExactRatio.of(60), Rel.LE));
    }

    /** The same difference held to one number is held at the years that differ by it, which are
     *  of the patterns that go with their difference only. */
    @Test
    void aDifferenceHeldToOneNumberIsNotHeldAtEveryPattern() {
        List<EveryPatternOfYears.Year> difference = List.of(year(0, 1, 0), year(1, -1, 0));
        assertFalse(EveryPatternOfYears.heldBy(difference, 2, ExactRatio.of(-60), Rel.EQ));
    }

    /** A year held to the last years of the calendar leaves no stretch of two cycles. */
    @Test
    void aYearHeldToTheEndOfTheCalendarIsNotHeldAtEveryPattern() {
        assertFalse(EveryPatternOfYears.heldBy(List.of(year(0, 1, 0)), 1,
                ExactRatio.of(-999_999_999), Rel.GE));
    }

    /** A date moved a day back is in the year before it on the first of January only, so that
     *  month and day is not the same in the year asked of the moved date. */
    @Test
    void aDateAShiftTakesToAnotherYearInSomeYearsIsNotTheSameInEveryYear() {
        // Nothing asked of the parts: only whether the date stays in its year after the shift.
        int withNoShift = DatesThatStandInEveryYear.of(List.of(), List.of()).size();
        int shiftedBack = DatesThatStandInEveryYear.of(List.of(),
                List.of(DateTranslation.none().thenAddDays(-1))).size();
        assertEquals(withNoShift - 1, shiftedBack);
    }
}
