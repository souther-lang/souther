package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Statements that weigh the same terms alike hold a form to a set of the line, and what that set
 * leaves is worked out from where each statement crosses it. A statement, and the relation asked
 * of it, are written as the compiler holds them: {@code weight * term + constant} against nought.
 */
class WhatStatementsOfOneFormDecideTest {

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final NumericTerm Y = new NumericTerm.ValueOf(TermPath.of("y"));

    private static TakenConstraint.Affine on(NumericTerm term, long weight, long constant,
                                             Rel rel) {
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant),
                Map.of(term, ExactRatio.of(weight))), rel);
    }

    private static boolean noRowArrives(TakenConstraint.Affine... stated) {
        return WhatStatementsOfOneFormDecide.of(List.of(stated), null).noRowArrives();
    }

    private static boolean decides(TakenConstraint.Affine asked,
                                   TakenConstraint.Affine... stated) {
        return WhatStatementsOfOneFormDecide.of(List.of(stated), asked).relationIsDecided();
    }

    @Test
    void statementsThatHoldTheFormNowhereLeaveNoRow() {
        assertTrue(noRowArrives(on(X, 1, 0, Rel.LE), on(X, 1, 0, Rel.GT)));
    }

    @Test
    void aNegativeFactorTurnsTheOrderingOfAStatement() {
        assertTrue(noRowArrives(on(X, 1, -5, Rel.GE), on(X, -2, 8, Rel.GE)), "x >= 5, 4 >= x");
    }

    @Test
    void aLevelHeldFromBothSidesLeavesThatPoint() {
        assertFalse(noRowArrives(on(X, 1, -5, Rel.GE), on(X, 1, -5, Rel.LE)));
    }

    @Test
    void aRelationThatCrossesWhatTheWayLeavesIsNotDecided() {
        // x >= 0 leaves x at nine and at ten, which x - 10 >= 0 tells apart.
        assertFalse(decides(on(X, 1, -10, Rel.GE), on(X, 1, 0, Rel.GE)));
        assertTrue(decides(on(X, 1, 10, Rel.GE), on(X, 1, 0, Rel.GE)), "x + 10 >= 0");
    }

    @Test
    void aRelationOfALevelTheWayStaysOnOneSideOfIsDecided() {
        TakenConstraint.Affine atLeast76 = on(X, 1, -76, Rel.GE);

        assertTrue(decides(on(X, 1, -70, Rel.GE), atLeast76), "x >= 70");
        assertFalse(decides(on(X, 1, -80, Rel.GE), atLeast76), "x >= 80");
    }

    @Test
    void aRelationIsDecidedInTheScaleAndSignItIsWrittenIn() {
        assertTrue(decides(on(X, -2, 100, Rel.LE), on(X, 1, -76, Rel.GE)), "-2x + 100 <= 0");
    }

    @Test
    void anEqualityOrAnInequalityIsDecidedOnlyWhereTheWayExcludesOrFixesTheLevel() {
        TakenConstraint.Affine atLeast76 = on(X, 1, -76, Rel.GE);

        assertTrue(decides(on(X, 1, -70, Rel.EQ), atLeast76), "x == 70 holds nowhere");
        assertFalse(decides(on(X, 1, -76, Rel.EQ), atLeast76), "x == 76 holds at one point");
        assertFalse(decides(on(X, 1, -76, Rel.NE), atLeast76), "x != 76 holds at the others");
    }

    @Test
    void aStrictStatementKeepsItsLevelOutOfTheWay() {
        assertTrue(decides(on(X, 1, -76, Rel.GE), on(X, 1, -76, Rel.GT)), "x > 76 gives x >= 76");
        assertFalse(decides(on(X, 1, -76, Rel.GT), on(X, 1, -76, Rel.GE)), "x >= 76 leaves 76");
    }

    @Test
    void aStatementOfAnotherFormDecidesNothing() {
        assertFalse(decides(on(X, 1, -70, Rel.GE), on(Y, 1, -76, Rel.GE)));
    }

    @Test
    void aTermInsideAContainerIsLeftOutBecauseEachStatementMayBeOfAnotherElement() {
        NumericTerm element = new NumericTerm.ValueOf(TermPath.of("xs").element());

        assertEquals(WhatStatementsOfOneFormDecide.Verdict.NOTHING,
                WhatStatementsOfOneFormDecide.of(
                        List.of(on(element, 1, 0, Rel.LE), on(element, 1, 0, Rel.GT)), null));
    }
}
