package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.IntSum;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether some value of one term completes every operation of a row, with the other standing, is
 * worked out from the operations: each is a run of the term, and the row exists where the runs
 * meet. It is not found by trying values, which finds a value only where one happens to be tried.
 */
class ARowIsCompletedByTheOtherTermWhereTheOperationsMeetTest {

    private static final String X = "x";
    private static final String Y = "y";

    private static BigInteger n(long value) {
        return BigInteger.valueOf(value);
    }

    private static IntSum sum(long xWeight, long yWeight, long constant, long least,
                              long greatest) {
        Map<Object, ExactRatio> coefs = new LinkedHashMap<>();
        if (xWeight != 0) {
            coefs.put(X, ExactRatio.of(n(xWeight)));
        }
        if (yWeight != 0) {
            coefs.put(Y, ExactRatio.of(n(yWeight)));
        }
        return new IntSum(coefs, ExactRatio.of(n(constant)), n(least), n(greatest));
    }

    private static RowsComputed told(IntSum... sums) {
        return RowsComputed.upTo(null)
                .withOperations(Operations.read(List.of(sums), true));
    }

    private static boolean completes(RowsComputed rows, long x, BigInteger least,
                                     BigInteger greatest) {
        return rows.aWholeValueCompletes(X, ExactRatio.of(n(x)), Y, least, greatest);
    }

    /** Two operations that both hold only inside the run of the term, at neither end of it. */
    @Test
    void operationsThatMeetOnlyInsideTheRunAreMetThere() {
        // 0 <= y - 3 <= 10 holds from 3, and -10 <= y - 7 <= 0 to 7.
        RowsComputed rows = told(sum(0, 1, -3, 0, 10), sum(0, 1, -7, -10, 0));

        assertTrue(completes(rows, 0, n(0), n(10)));
    }

    @Test
    void operationsThatMeetNowhereInTheRunAreNoRow() {
        // From 3 up, and up to 2 down from -3.
        RowsComputed rows = told(sum(0, 1, -3, 0, 10), sum(0, 1, 0, -10, 2));

        assertFalse(completes(rows, 0, n(-5), n(10)));
    }

    @Test
    void theRunOfTheTermCutsWhatTheOperationsAllow() {
        RowsComputed rows = told(sum(0, 1, 0, 3, 7));

        assertTrue(completes(rows, 0, n(7), n(9)));
        assertFalse(completes(rows, 0, n(8), n(9)));
        assertFalse(completes(rows, 0, n(0), n(2)));
    }

    @Test
    void aTermWithNoEndIsCutByTheOperationsAlone() {
        RowsComputed rows = told(sum(0, 1, 0, 3, 7));

        assertTrue(completes(rows, 0, null, null));
        assertTrue(completes(rows, 0, null, n(3)));
        assertFalse(completes(rows, 0, null, n(2)));
        assertFalse(completes(rows, 0, n(8), null));
    }

    @Test
    void aWeightBelowNoughtTurnsTheRunRound() {
        // 3 <= 10 - y <= 7 holds for y from 3 to 7.
        RowsComputed rows = told(sum(0, -1, 10, 3, 7));

        assertTrue(completes(rows, 0, n(7), n(20)));
        assertFalse(completes(rows, 0, n(8), n(20)));
    }

    @Test
    void aWeightOfTwoLeavesOnlyTheWholeValuesInTheRun() {
        // 3 <= 2y <= 3 holds at no whole y: it needs one and a half.
        RowsComputed rows = told(sum(0, 2, 0, 3, 3));

        assertFalse(completes(rows, 0, n(0), n(10)));
        assertTrue(completes(told(sum(0, 2, 0, 3, 4)), 0, n(0), n(10)));
    }

    /** The shape of a date moved by a count: the date nearest nought is not where it completes. */
    @Test
    void aSumOfTwoCompletesAtTheOtherEndOfTheTypeWhereNothingNearNoughtDoes() {
        long least = -365_243_219_162L;
        long greatest = 365_241_780_471L;
        RowsComputed rows = told(sum(1, 1, 0, least, greatest));
        long count = 365_243_239_981L;

        assertFalse(rows.computedAt(() -> Map.of(X, ExactRatio.of(n(count)),
                Y, ExactRatio.ZERO)));
        assertTrue(completes(rows, count, n(least), n(greatest)));
        // Past twice the type's length every sum is past an end, whichever date it is moved from.
        assertFalse(completes(rows, greatest - least + 1 + greatest, n(least), n(greatest)));
        assertFalse(completes(rows, least - greatest - 1 + least, n(least), n(greatest)));
    }

    @Test
    void anOperationThatDoesNotReadTheTermsIsHeldAtTheValueAsked() {
        RowsComputed rows = told(sum(1, 0, 0, 0, 5));

        assertTrue(completes(rows, 3, n(0), n(10)));
        assertFalse(completes(rows, 6, n(0), n(10)));
    }

    @Test
    void everyOperationHasToBeMetAndNotOnlyTheOneThatEndsUpInsideTheType() {
        // x + y stays inside at any y of the run, and y + 100 does at none of them.
        RowsComputed rows = told(sum(0, 1, 100, 0, 10), sum(1, 1, 0, 0, 1000));

        assertFalse(completes(rows, 5, n(0), n(10)));
    }

    @Test
    void anOperationNotAllToldIsNoRowShown() {
        RowsComputed some = RowsComputed.upTo(null)
                .withOperations(Operations.read(List.of(sum(0, 1, 0, 0, 10)), false));

        assertFalse(completes(some, 0, n(0), n(10)));
    }

    @Test
    void anOperationReadingATermNeitherNamesAndNoneHoldsStillIsNoRowShown() {
        IntSum other = new IntSum(Map.of("z", ExactRatio.ONE, Y, ExactRatio.ONE), ExactRatio.ZERO,
                n(0), n(10));

        assertFalse(completes(told(other), 0, n(0), n(10)));
        assertTrue(completes(told(other).withTheRestAt(Map.of("z", ExactRatio.of(n(2)))), 0, n(0),
                n(10)));
    }
}
