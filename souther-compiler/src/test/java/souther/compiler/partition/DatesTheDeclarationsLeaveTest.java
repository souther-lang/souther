package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DatePartsLeft;
import souther.compiler.check.RuleOfDateParts;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A date is shown for a part among some values only where one date of the class, the ends and
 * every rule of two parts has the part there; a run is asked whole, and a value of it no date has
 * is not taken for the run. Each date found is held to the rule and the values as written, worked
 * out with {@link LocalDate}.
 */
class DatesTheDeclarationsLeaveTest {

    private static final DateTranslation EVERY_DAY = DateTranslation.none();

    /** {@code Date.day(value) - Date.month(value) >= 28}: January from the twenty-ninth, March
     *  on its thirty-first, and no day of February. */
    private static final RuleOfDateParts PAST_THE_MONTH = new RuleOfDateParts(Map.of(
            TakenAs.DatePart.DAY, ExactRatio.ONE, TakenAs.DatePart.MONTH, ExactRatio.of(-1)),
            ExactRatio.of(-28), Rel.GE);

    private static boolean holdsPastTheMonth(LocalDate date) {
        return date.getDayOfMonth() - date.getMonthValue() >= 28;
    }

    private static LevelRegion from(long least, long most) {
        return LevelRegion.of(new LevelInterval(level(least), level(most)));
    }

    private static Bound level(long at) {
        return Bound.at(new Level.OfTheQuantity(ExactRatio.of(at)), true);
    }

    private static DatesThatHoldEveryStatement.Answer months(DatePartsLeft left,
                                                             List<RuleOfDateParts> rules,
                                                             LevelRegion asked) {
        return DatesTheDeclarationsLeave.withThePartIn(left, rules, EVERY_DAY,
                TakenAs.DatePart.MONTH, asked, EVERY_DAY);
    }

    private static LocalDate theDate(DatesThatHoldEveryStatement.Answer answer) {
        return assertInstanceOf(DatesThatHoldEveryStatement.Found.class, answer).dates()
                .getFirst();
    }

    /** February and March: the month next to the line is one no date of the rule has, and the
     *  run is shown by March. */
    @Test
    void aRunIsShownByAValueOfItAwayFromTheLine() {
        LocalDate date = theDate(months(DatePartsLeft.EVERY_DATE, List.of(PAST_THE_MONTH),
                from(2, 3)));

        assertTrue(holdsPastTheMonth(date), date.toString());
        assertEquals(3, date.getMonthValue());
    }

    @Test
    void aValueNoDateOfTheRuleHasIsNotShown() {
        assertFalse(months(DatePartsLeft.EVERY_DATE, List.of(PAST_THE_MONTH), from(2, 2))
                instanceof DatesThatHoldEveryStatement.Found);
        assertFalse(months(DatePartsLeft.EVERY_DATE, List.of(PAST_THE_MONTH), from(4, 12))
                instanceof DatesThatHoldEveryStatement.Found);
    }

    /** No rule of two parts: the class alone. February has no thirtieth, and the run from the
     *  twenty-eighth is shown by a day it has. */
    @Test
    void withNoRuleTheClassIsWalkedForTheRun() {
        DatePartsLeft february = new DatePartsLeft(Map.of(TakenAs.DatePart.MONTH,
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(2)),
                        Endpoint.inclusive(Count.of(2)))));

        LocalDate date = theDate(DatesTheDeclarationsLeave.withThePartIn(february, List.of(),
                EVERY_DAY, TakenAs.DatePart.DAY, from(28, 31), EVERY_DAY));
        assertEquals(2, date.getMonthValue());
        assertTrue(date.getDayOfMonth() >= 28, date.toString());
        assertFalse(DatesTheDeclarationsLeave.withThePartIn(february, List.of(), EVERY_DAY,
                TakenAs.DatePart.DAY, from(30, 31), EVERY_DAY)
                instanceof DatesThatHoldEveryStatement.Found);
    }

    /** Past every month the calendar has, nothing is asked: none hold. */
    @Test
    void aRunPastTheCalendarHoldsNone() {
        assertEquals(DatesThatHoldEveryStatement.Otherwise.NONE_HOLD,
                months(DatePartsLeft.EVERY_DATE, List.of(PAST_THE_MONTH), from(13, 20)));
    }
}
