package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.PlacesTheRulesRead;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class TheCountOfRecordsBuiltUnderARuleIsOneForTheOutermostRecordTest {

    /**
     * Two fields of one record, each holding a sum built under a rule of the record: what one
     * spends the other does not have, and so does everything built under either.
     */
    @Test
    void siblingsAndTheirDescendantsSpendOneCount() {
        Partitions.RulesAround outermost = Partitions.RulesAround.NONE.sharing();
        Partitions.RulesAround first = outermost.aroundTheField(PlacesTheRulesRead.NONE, null, "p");
        Partitions.RulesAround second = outermost.aroundTheField(PlacesTheRulesRead.NONE, null, "q");
        Partitions.RulesAround below = first.aroundTheField(PlacesTheRulesRead.NONE, null, "r");
        int most = CompositionBudget.CASES_A_RULE_ABOVE_IS_PLANNED_UNDER.maximum();

        for (int i = 0; i < most; i++) {
            assertTrue(second.hasLeft());
            (i % 2 == 0 ? first : below).spend();
        }

        assertFalse(second.hasLeft());
        assertFalse(first.hasLeft());
        assertFalse(below.hasLeft());
    }

    /** And a record built on its own, under no other, begins a count of its own. */
    @Test
    void nothingAroundHasNoCountUntilOneBegins() {
        assertFalse(Partitions.RulesAround.NONE.hasLeft());
        assertTrue(Partitions.RulesAround.NONE.sharing().hasLeft());
    }
}
