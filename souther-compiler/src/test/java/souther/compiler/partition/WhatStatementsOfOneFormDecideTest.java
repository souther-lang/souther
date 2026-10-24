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

    /** {@code a * x + b * y + constant} against nought. */
    private static TakenConstraint.Affine over(long a, long b, long constant, Rel rel) {
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant),
                Map.of(X, ExactRatio.of(a), Y, ExactRatio.of(b))), rel);
    }

    /** Whether the statements are met by a row beside the line of {@code asked}. */
    private static boolean leavesRoom(TakenConstraint.Affine asked,
                                      TakenConstraint.Affine... stated) {
        List<TakenConstraint.Affine> met = WhatStatementsOfOneFormDecide
                .leavingRoomAroundTheLine(List.of(stated), asked);
        return met.equals(List.of(stated));
    }

    /** {@code x + y < 200}, whose line is where the sum is two hundred. */
    private static final TakenConstraint.Affine BELOW_200 = over(1, 1, -200, Rel.LT);

    @Test
    void anOrderHoldingTheFormOnBothSidesOfTheLineLeavesRoomAroundIt() {
        assertTrue(leavesRoom(BELOW_200, over(1, 1, -100, Rel.GE)), "x + y >= 100");
        assertTrue(leavesRoom(BELOW_200, over(1, 1, -199, Rel.GE)),
                "x + y >= 199 holds at the last value below the line, which it ends at");
        assertTrue(leavesRoom(BELOW_200, over(-1, -1, 100, Rel.LE)), "-x - y <= -100");
        assertTrue(leavesRoom(BELOW_200, over(1, 1, -100, Rel.GT)), "x + y > 100");
    }

    @Test
    void anOrderEndingBeforeTheValueARowAtTheLineNeedsLeavesNoRoom() {
        assertFalse(leavesRoom(BELOW_200, over(1, 1, -200, Rel.GE)), "x + y >= 200");
        assertFalse(leavesRoom(BELOW_200, over(1, 1, -200, Rel.GT)), "x + y > 200");
        assertFalse(leavesRoom(BELOW_200, over(1, 1, -199, Rel.GT)),
                "x + y > 199 leaves 199 out, which a row below the line is at");
        assertFalse(leavesRoom(BELOW_200, over(1, 1, -198, Rel.LE)),
                "x + y <= 198 ends before the last value below the line");
        assertFalse(leavesRoom(BELOW_200, over(1, 1, -200, Rel.LE)),
                "x + y <= 200 ends before the first value past the line");
        assertTrue(leavesRoom(BELOW_200, over(1, 1, -201, Rel.LE)),
                "x + y <= 201 ends at the value a row beyond the line is at");
    }

    @Test
    void anEqualityOrADisequalityIsNotAnIntervalAndLeavesNoRoom() {
        assertFalse(leavesRoom(BELOW_200, over(1, 1, -100, Rel.EQ)), "x + y == 100");
        assertFalse(leavesRoom(BELOW_200, over(1, 1, -100, Rel.NE)), "x + y != 100");
        assertEquals(List.of(), WhatStatementsOfOneFormDecide.leavingRoomAroundTheLine(
                List.of(over(1, 1, -100, Rel.GE), over(1, 1, -150, Rel.NE)), BELOW_200),
                "one statement that is no order takes the others with it");
    }

    @Test
    void aStatementOfAnotherFormLeavesNoRoomForTheFormAsked() {
        assertFalse(leavesRoom(BELOW_200, over(1, -1, 0, Rel.GE)), "x - y >= 0");
        assertFalse(leavesRoom(BELOW_200, on(X, 1, 0, Rel.GE)), "x >= 0");
        assertEquals(List.of(over(1, 1, -100, Rel.GE)),
                WhatStatementsOfOneFormDecide.leavingRoomAroundTheLine(
                        List.of(over(1, 1, -100, Rel.GE), over(1, -1, 0, Rel.GE)), BELOW_200),
                "the one of the form asked is met, the other stays");
    }

    @Test
    void aStatementMetIsEveryOneOfTheFormAsked() {
        assertEquals(List.of(), WhatStatementsOfOneFormDecide.leavingRoomAroundTheLine(
                List.of(over(1, 1, -100, Rel.GE), over(1, 1, -200, Rel.GE)), BELOW_200),
                "one statement not met takes the others with it");
    }

    @Test
    void theRoomAskedForIsTheGreatestWeightOfTheForm() {
        TakenConstraint.Affine weighed = over(2, 1, -200, Rel.LT);

        assertTrue(leavesRoom(weighed, over(2, 1, -198, Rel.GE)), "2x + y >= 198, two away");
        assertFalse(leavesRoom(weighed, over(2, 1, -199, Rel.GE)), "2x + y >= 199");
        assertTrue(leavesRoom(weighed, over(2, 1, -202, Rel.LE)), "2x + y <= 202, two beyond");
        assertFalse(leavesRoom(weighed, over(2, 1, -201, Rel.LE)), "2x + y <= 201");
        assertTrue(leavesRoom(over(-3, 1, -200, Rel.LT), over(-3, 1, -197, Rel.GE)),
                "the greatest of the weights' magnitudes is three");
        assertFalse(leavesRoom(over(-3, 1, -200, Rel.LT), over(-3, 1, -199, Rel.GE)),
                "-3x + y >= 199 is not three below the line");
    }

    @Test
    void aTermInsideAContainerIsLeftOutBecauseEachStatementMayBeOfAnotherElement() {
        NumericTerm element = new NumericTerm.ValueOf(TermPath.of("xs").element());

        assertEquals(WhatStatementsOfOneFormDecide.Verdict.NOTHING,
                WhatStatementsOfOneFormDecide.of(
                        List.of(on(element, 1, 0, Rel.LE), on(element, 1, 0, Rel.GT)), null));
    }
}
