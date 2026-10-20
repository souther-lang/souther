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
 * leaves is worked out from where each statement crosses it.
 */
class WhatStatementsOfOneFormDecideTest {

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final NumericTerm Y = new NumericTerm.ValueOf(TermPath.of("y"));

    /** {@code weight * term + constant rel 0}. */
    private static TakenConstraint.Affine on(NumericTerm term, long weight, long constant,
                                             Rel rel) {
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant),
                Map.of(term, ExactRatio.of(weight))), rel);
    }

    private static boolean noRowArrives(TakenConstraint.Affine... stated) {
        return WhatStatementsOfOneFormDecide.of(List.of(stated), null, null, Rel.EQ)
                .noRowArrives();
    }

    private static boolean decided(NumericTerm form, long weight, long level, Rel relation,
                                   TakenConstraint.Affine... stated) {
        return WhatStatementsOfOneFormDecide.of(List.of(stated), Map.of(form,
                ExactRatio.of(weight)), ExactRatio.of(level), relation).relationIsDecided();
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
    void aRelationIsDecidedWhereEveryPointTheStatementsLeaveGivesItOneAnswer() {
        TakenConstraint.Affine atLeast76 = on(X, 1, -76, Rel.GE);

        assertTrue(decided(X, 1, 70, Rel.GE, atLeast76), "x >= 70 under x >= 76");
        assertFalse(decided(X, 1, 80, Rel.GE, atLeast76), "x >= 80 under x >= 76");
    }

    @Test
    void aRelationIsDecidedInTheScaleAndSignItIsAskedIn() {
        assertTrue(decided(X, -2, -100, Rel.LE, on(X, 1, -76, Rel.GE)), "-2x <= -100");
    }

    @Test
    void aStatementOfAnotherFormDecidesNothing() {
        assertFalse(decided(X, 1, 70, Rel.GE, on(Y, 1, -76, Rel.GE)));
    }

    @Test
    void aTermInsideAContainerIsLeftOutBecauseEachStatementMayBeOfAnotherElement() {
        NumericTerm element = new NumericTerm.ValueOf(TermPath.of("xs").element());

        assertEquals(WhatStatementsOfOneFormDecide.Verdict.NOTHING,
                WhatStatementsOfOneFormDecide.of(
                        List.of(on(element, 1, 0, Rel.LE), on(element, 1, 0, Rel.GT)), null, null,
                        Rel.EQ));
    }
}
