package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How far a row got says which of the three sets its case is in, and a row gets to them in order.
 *
 * <p>A row that held was applied and a row that was applied was built, so being in a later set is
 * being in every earlier one. The order of the constants is what says so, which is why it is
 * asked here and not left to whoever next adds a constant.
 */
class AnUnreadRowIsInTheSetsItsRowGotAsFarAsTest {

    private static final InputCaseEvidence.Reached SPECIFIED = InputCaseEvidence.Reached.SPECIFIED;
    private static final InputCaseEvidence.Reached EXECUTED = InputCaseEvidence.Reached.EXECUTED;
    private static final InputCaseEvidence.Reached VERIFIED = InputCaseEvidence.Reached.VERIFIED;
    private static final InputCaseEvidence.Reached NOWHERE = InputCaseEvidence.Reached.NOWHERE;

    @Test
    void theSetsAreInTheOrderARowGetsToThem() {
        assertEquals(List.of(SPECIFIED, EXECUTED, VERIFIED), InputCaseEvidence.Reached.SETS);
    }

    @Test
    void aRowIsInEverySetUpToTheOneItGotTo() {
        assertTrue(VERIFIED.isIn(VERIFIED) && VERIFIED.isIn(EXECUTED) && VERIFIED.isIn(SPECIFIED));
        assertTrue(EXECUTED.isIn(EXECUTED) && EXECUTED.isIn(SPECIFIED));
        assertTrue(SPECIFIED.isIn(SPECIFIED));
    }

    @Test
    void aRowIsInNoSetPastTheOneItGotTo() {
        assertFalse(EXECUTED.isIn(VERIFIED));
        assertFalse(SPECIFIED.isIn(EXECUTED));
        assertFalse(SPECIFIED.isIn(VERIFIED));
    }

    @Test
    void aRowThatGotNowhereIsInNone() {
        for (InputCaseEvidence.Reached set : InputCaseEvidence.Reached.SETS) {
            assertFalse(NOWHERE.isIn(set), "nowhere is in " + set);
        }
    }
}
