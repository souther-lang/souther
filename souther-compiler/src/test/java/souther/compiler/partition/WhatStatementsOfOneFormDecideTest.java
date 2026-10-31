package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
                .leavingRoomAroundTheLine(List.of(stated), asked, false);
        return met.equals(List.of(stated));
    }

    /** The same, for numbers that move in whole steps. */
    private static boolean leavesRoomInWholeSteps(TakenConstraint.Affine asked,
                                                  TakenConstraint.Affine... stated) {
        List<TakenConstraint.Affine> met = WhatStatementsOfOneFormDecide
                .leavingRoomAroundTheLine(List.of(stated), asked, true);
        return met.equals(List.of(stated));
    }

    @Test
    void aRelationHoldingBelowTheLineIsFlippedBetweenTheLastValueBelowAndTheLine() {
        TakenConstraint.Affine below = over(1, 1, -50, Rel.LT);

        assertTrue(leavesRoomInWholeSteps(below, over(1, 1, -50, Rel.LE)),
                "x + y <= 50 holds at 49 and 50, the two values x + y < 50 flips between");
        assertFalse(leavesRoom(below, over(1, 1, -50, Rel.LE)),
                "beside the line in a step either way, 51 is asked too");
        assertFalse(leavesRoomInWholeSteps(below, over(1, 1, -49, Rel.LE)),
                "x + y <= 49 ends before 50");
        assertTrue(leavesRoomInWholeSteps(below, over(1, 1, -49, Rel.GE)),
                "x + y >= 49 holds at 49 and above");
    }

    @Test
    void theOtherRelationsAreFlippedBetweenTheirOwnTwoValues() {
        assertTrue(leavesRoomInWholeSteps(over(1, 1, -50, Rel.GT), over(1, 1, -50, Rel.GE)),
                "x + y > 50 flips between 50 and 51, and x + y >= 50 holds at both");
        assertFalse(leavesRoomInWholeSteps(over(1, 1, -50, Rel.GT), over(1, 1, -51, Rel.GE)),
                "x + y >= 51 leaves 50 out");
        assertTrue(leavesRoomInWholeSteps(over(1, 1, -50, Rel.LE), over(1, 1, -51, Rel.LE)),
                "x + y <= 50 flips between 50 and 51");
        assertFalse(leavesRoomInWholeSteps(over(1, 1, -50, Rel.LE), over(1, 1, -50, Rel.LE)),
                "x + y <= 50 ends before 51");
        assertTrue(leavesRoomInWholeSteps(over(1, 1, -50, Rel.GE), over(1, 1, -50, Rel.LE)),
                "x + y >= 50 flips between 49 and 50");
    }

    @Test
    void aWeightOfTwoStillAsksForTheRangeASingleStepCanCross() {
        TakenConstraint.Affine weighed = over(2, 1, -50, Rel.LT);

        assertTrue(leavesRoomInWholeSteps(weighed, over(2, 1, -51, Rel.LE)),
                "2x + y < 50 flips between a value in 48..49 and one in 50..51");
        assertFalse(leavesRoomInWholeSteps(weighed, over(2, 1, -50, Rel.LE)),
                "2x + y <= 50 ends before 51");
    }

    @Test
    void aWeightThatIsNoWholeNumberKeepsTheRangeAWholeWeightEitherSide() {
        TakenConstraint.Affine halves = new TakenConstraint.Affine(new LinearForm<>(
                ExactRatio.of(-50), Map.of(X, ExactRatio.of(1),
                        Y, ExactRatio.of(BigInteger.ONE, BigInteger.TWO))), Rel.LT);

        assertFalse(leavesRoomInWholeSteps(halves, over(1, 1, -50, Rel.LE)),
                "x + y <= 50 ends before 51, which a half step can still reach");
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
                List.of(over(1, 1, -100, Rel.GE), over(1, 1, -150, Rel.NE)), BELOW_200, false),
                "one statement that is no order takes the others with it");
    }

    @Test
    void aStatementOfAnotherFormLeavesNoRoomForTheFormAsked() {
        assertFalse(leavesRoom(BELOW_200, over(1, -1, 0, Rel.GE)), "x - y >= 0");
        assertFalse(leavesRoom(BELOW_200, on(X, 1, 0, Rel.GE)), "x >= 0");
        assertEquals(List.of(over(1, 1, -100, Rel.GE)),
                WhatStatementsOfOneFormDecide.leavingRoomAroundTheLine(
                        List.of(over(1, 1, -100, Rel.GE), over(1, -1, 0, Rel.GE)), BELOW_200, false),
                "the one of the form asked is met, the other stays");
    }

    @Test
    void aStatementMetIsEveryOneOfTheFormAsked() {
        assertEquals(List.of(), WhatStatementsOfOneFormDecide.leavingRoomAroundTheLine(
                List.of(over(1, 1, -100, Rel.GE), over(1, 1, -200, Rel.GE)), BELOW_200, false),
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

    /**
     * Statements of one form leave a point of the line exactly where some value of the form
     * stands on the right side of every one of them. Every set of up to three statements of a few
     * weights, constants and relations is held to the points between, at and beyond where they
     * cross, which are at quarters of a unit when the weights are one and two.
     */
    @Test
    void whatStatementsLeaveIsWhatEveryValueOfTheFormBetweenTheirCrossingsLeaves() {
        List<Written> all = new ArrayList<>();
        for (long weight : new long[] {1, -2}) {
            for (long constant : new long[] {-2, 0, 3}) {
                for (Rel rel : Rel.values()) {
                    all.add(new Written(weight, constant, rel));
                }
            }
        }
        List<Written> asks = List.of(new Written(1, -1, Rel.GE), new Written(-2, 3, Rel.EQ),
                new Written(1, 0, Rel.NE));
        for (int first = 0; first < all.size(); first++) {
            for (int second = first; second < all.size(); second++) {
                for (int third = second; third < all.size(); third++) {
                    List<Written> stated = List.of(all.get(first), all.get(second),
                            all.get(third));
                    for (Written asked : asks) {
                        assertEquals(everyValueBetween(stated, asked),
                                WhatStatementsOfOneFormDecide.of(
                                        stated.stream().map(Written::affine).toList(),
                                        asked.affine()),
                                stated + " asking " + asked);
                    }
                }
            }
        }
    }

    /** A statement as {@code weight * x + constant} against nought. */
    private record Written(long weight, long constant, Rel rel) {

        TakenConstraint.Affine affine() {
            return on(X, weight, constant, rel);
        }

        boolean holdsAt(int quarters) {
            return rel.holds(Long.signum(weight * quarters + constant * 4));
        }
    }

    private static WhatStatementsOfOneFormDecide.Verdict everyValueBetween(
            List<Written> stated, Written asked) {
        boolean any = false;
        Set<Boolean> askedAt = new HashSet<>();
        for (int quarters = -40; quarters <= 40; quarters++) {
            boolean holdsAll = true;
            for (Written each : stated) {
                holdsAll &= each.holdsAt(quarters);
            }
            if (holdsAll) {
                any = true;
                askedAt.add(asked.holdsAt(quarters));
            }
        }
        return new WhatStatementsOfOneFormDecide.Verdict(!any, any && askedAt.size() == 1);
    }

    @Test
    void aTermInsideAContainerIsLeftOutBecauseEachStatementMayBeOfAnotherElement() {
        NumericTerm element = new NumericTerm.ValueOf(TermPath.of("xs").element());

        assertEquals(WhatStatementsOfOneFormDecide.Verdict.NOTHING,
                WhatStatementsOfOneFormDecide.of(
                        List.of(on(element, 1, 0, Rel.LE), on(element, 1, 0, Rel.GT)), null));
    }
}
