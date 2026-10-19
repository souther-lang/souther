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

    /** {@code weight * x + constant rel 0}. */
    private static TakenConstraint.Affine on(NumericTerm term, long weight, long constant,
                                             Rel rel) {
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant),
                Map.of(term, ExactRatio.of(weight))), rel);
    }

    private static WhatStatementsOfOneFormDecide.Verdict askedOfX(
            List<TakenConstraint.Affine> stated, long level, Rel relation) {
        return WhatStatementsOfOneFormDecide.of(stated, Map.of(X, ExactRatio.ONE),
                ExactRatio.of(level), relation);
    }

    @Test
    void statementsThatHoldTheFormNowhereLeaveNoRow() {
        var verdict = WhatStatementsOfOneFormDecide.of(
                List.of(on(X, 100, 0, Rel.LE), on(X, 100, 0, Rel.GT)), null, null, Rel.EQ);

        assertTrue(verdict.noRowArrives());
    }

    @Test
    void aFactorAndASignDoNotHideThatTwoStatementsAreOfOneForm() {
        var verdict = WhatStatementsOfOneFormDecide.of(
                List.of(on(X, 1, -5, Rel.GE), on(X, -2, 8, Rel.GE)), null, null, Rel.EQ);

        assertTrue(verdict.noRowArrives(), "x >= 5 and 4 >= x");
        assertFalse(WhatStatementsOfOneFormDecide.of(
                List.of(on(X, 1, -5, Rel.GE), on(X, -2, 12, Rel.GE)), null, null, Rel.EQ)
                .noRowArrives(), "x >= 5 and 6 >= x leave five and six");
    }

    @Test
    void aSingleLevelBoundsFromBothSidesLeavesThatPoint() {
        var verdict = WhatStatementsOfOneFormDecide.of(
                List.of(on(X, 1, -5, Rel.GE), on(X, 1, -5, Rel.LE)), null, null, Rel.EQ);

        assertFalse(verdict.noRowArrives());
    }

    @Test
    void aRelationIsDecidedWhereTheStatementsLeaveItOneWayAtEveryPoint() {
        List<TakenConstraint.Affine> above75 = List.of(on(X, 1, -76, Rel.GE),
                on(X, 1, -75, Rel.GT));

        assertTrue(askedOfX(above75, 70, Rel.GE).relationIsDecided(), "x >= 70 under x >= 76");
        assertTrue(askedOfX(above75, 76, Rel.GE).relationIsDecided(), "x >= 76 under x >= 76");
        assertTrue(askedOfX(above75, 76, Rel.LT).relationIsDecided(), "x < 76 under x >= 76");
        assertFalse(askedOfX(above75, 80, Rel.GE).relationIsDecided(), "x >= 80 under x >= 76");
        assertFalse(askedOfX(above75, 77, Rel.GT).relationIsDecided(), "x > 77 under x >= 76");
    }

    @Test
    void theRelationIsDecidedByTheStatementsOfItsOwnFormAlone() {
        var verdict = WhatStatementsOfOneFormDecide.of(List.of(on(Y, 1, -76, Rel.GE)),
                Map.of(X, ExactRatio.ONE), ExactRatio.of(70), Rel.GE);

        assertFalse(verdict.relationIsDecided());
        assertFalse(verdict.noRowArrives());
    }

    @Test
    void aRelationOfAnotherScaleAndSignIsDecidedAsItsOwnForm() {
        var verdict = WhatStatementsOfOneFormDecide.of(List.of(on(X, 1, -76, Rel.GE)),
                Map.of(X, ExactRatio.of(-2)), ExactRatio.of(-100), Rel.LE);

        // -2x <= -100 is x >= 50, which x >= 76 meets.
        assertTrue(verdict.relationIsDecided());
    }

    @Test
    void aTermInsideAContainerIsNotTakenForOneStatementIsPerElement() {
        TermPath inside = TermPath.of("xs").element();
        NumericTerm element = new NumericTerm.ValueOf(inside);

        var verdict = WhatStatementsOfOneFormDecide.of(
                List.of(on(element, 1, 0, Rel.LE), on(element, 1, 0, Rel.GT)), null, null,
                Rel.EQ);

        assertEquals(WhatStatementsOfOneFormDecide.Verdict.NOTHING, verdict);
    }
}
