package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.PlacesTheRulesRead;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class TheCountOfRecordsBuiltUnderARuleIsOneForTheOutermostRecordTest {

    private static final int MOST = CompositionBudget.CASES_A_RULE_ABOVE_IS_PLANNED_UNDER.maximum();

    /**
     * Two fields of one record, each holding a sum built under a rule of the record: what one
     * takes the other does not have, and so does everything built under either.
     */
    @Test
    void siblingsAndTheirDescendantsTakeFromOneCount() {
        Partitions.RulesAround outermost = Partitions.RulesAround.NONE.sharing();
        Partitions.RulesAround first = outermost.aroundTheField(PlacesTheRulesRead.NONE, null, "p");
        Partitions.RulesAround second = outermost.aroundTheField(PlacesTheRulesRead.NONE, null, "q");
        Partitions.RulesAround below = first.aroundTheField(PlacesTheRulesRead.NONE, null, "r");

        for (int i = 0; i < MOST; i++) {
            assertTrue(second.hasLeft());
            assertTrue((i % 2 == 0 ? first : below).reserve());
        }

        assertFalse(second.hasLeft());
        assertFalse(first.reserve());
        assertFalse(below.reserve());
    }

    /**
     * A record asks for its count before what is built inside it does. With one left, the record
     * holds it and the record inside is refused — and is let through once the first is given back,
     * which is a record whose rules left it no value.
     */
    @Test
    void aRecordHoldsItsCountWhileTheRecordsInsideItAreBuilt() {
        Partitions.RulesAround outermost = Partitions.RulesAround.NONE.sharing();
        Partitions.RulesAround parent = outermost.aroundTheField(PlacesTheRulesRead.NONE, null, "p");
        Partitions.RulesAround child = parent.aroundTheField(PlacesTheRulesRead.NONE, null, "c");
        for (int i = 0; i < MOST - 1; i++) {
            assertTrue(outermost.reserve());
        }

        assertTrue(parent.reserve());
        assertFalse(child.reserve());
        parent.refund();
        assertTrue(child.reserve());
    }

    /** And a record built on its own, under no other, begins a count of its own. */
    @Test
    void nothingAroundHasNoCountUntilOneBegins() {
        assertFalse(Partitions.RulesAround.NONE.hasLeft());
        assertTrue(Partitions.RulesAround.NONE.sharing().hasLeft());
    }
}
