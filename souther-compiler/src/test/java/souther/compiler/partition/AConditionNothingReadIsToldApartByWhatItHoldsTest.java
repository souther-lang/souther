package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.meaning.WhyNotTaken;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;

/**
 * A condition nothing read is told apart from another by which condition of the reading it is and
 * by what stopped it, and its number is that of those two.
 *
 * <p>Pairing two paths looks up each column of one in the other, so a rule keyed by these is asked
 * their number again and again. That the number is kept must leave which conditions are equal where
 * it was.
 */
class AConditionNothingReadIsToldApartByWhatItHoldsTest {

    private static final WhyNotTaken ON_NO_ORDER =
            new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER);

    private static final WhyNotTaken NO_ALTERNATIVES =
            new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES);

    private static ConditionOccurrence occurrence(int ordinal) {
        return new ConditionOccurrence("decides", ConditionOccurrence.Reading.DECIDING, ordinal);
    }

    @Test
    void twoMadeApartFromTheSameThingsAreOneKey() {
        var first = new DecisionCondition.AConditionNotRead(occurrence(0), ON_NO_ORDER);
        var second = new DecisionCondition.AConditionNotRead(occurrence(0), ON_NO_ORDER);

        assertNotSame(first, second);
        assertEquals(first, second);
        assertEquals(first.hashCode(), second.hashCode());
        assertEquals("found", Map.of(first, "found").get(second));
    }

    @Test
    void anotherConditionOfTheReadingIsAnotherColumn() {
        assertNotEquals(
                new DecisionCondition.AConditionNotRead(occurrence(0), ON_NO_ORDER),
                new DecisionCondition.AConditionNotRead(occurrence(1), ON_NO_ORDER));
    }

    @Test
    void anotherReasonIsAnotherColumn() {
        assertNotEquals(
                new DecisionCondition.AConditionNotRead(occurrence(0), ON_NO_ORDER),
                new DecisionCondition.AConditionNotRead(occurrence(0), NO_ALTERNATIVES));
    }

    @Test
    void aReasonSaidTwiceIsSaidOnce() {
        var twice = new DecisionCondition.AConditionNotRead(
                occurrence(0), List.of(ON_NO_ORDER, ON_NO_ORDER));
        var once = new DecisionCondition.AConditionNotRead(occurrence(0), ON_NO_ORDER);

        assertEquals(once, twice);
        assertEquals(once.hashCode(), twice.hashCode());
        assertEquals(List.of(ON_NO_ORDER), twice.whys());
    }

    @Test
    void reasonsInAnotherOrderAreAnotherColumn() {
        assertNotEquals(
                new DecisionCondition.AConditionNotRead(
                        occurrence(0), List.of(ON_NO_ORDER, NO_ALTERNATIVES)),
                new DecisionCondition.AConditionNotRead(
                        occurrence(0), List.of(NO_ALTERNATIVES, ON_NO_ORDER)));
    }
}
