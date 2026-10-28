package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.IntSum;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A type with no greatest value says that no size stops a run, and nothing else. A number built
 * into a type with an invariant, or an operation a comparison works out, stops a row of it all
 * the same, and a row is computed only where what the reading told of the program says so.
 */
class WhereATypeHasNoGreatestValueTheProgramCanStillStopARowTest {

    private static final ExactRatio[] NO_ADDENDS = new ExactRatio[0];

    private static IntSum between(int least, int greatest) {
        return new IntSum(Map.of("a", ExactRatio.ONE), ExactRatio.ZERO,
                BigInteger.valueOf(least), BigInteger.valueOf(greatest));
    }

    private static boolean computedAt(RowsComputed rows, int a) {
        return rows.rowIsComputed(() -> NO_ADDENDS, () -> Map.of("a", ExactRatio.of(a)));
    }

    @Test
    void noOperationIsSaidOfAProgramAddingTheFormUp() {
        RowsComputed rows = RowsComputed.ENDLESS;
        assertTrue(computedAt(rows, 1_000));
        assertTrue(rows.nothingStopsARow());
    }

    @Test
    void anUntoldOperationShowsNoRowComputedWhateverTheTypeHolds() {
        RowsComputed rows = RowsComputed.ENDLESS.withOperations(new Operations(List.of(), Told.SOME));
        assertFalse(computedAt(rows, 0));
        assertFalse(rows.nothingStopsARow());
        assertFalse(rows.farthestRowsAreComputed(List.of(), ExactRatio.ZERO, ExactRatio.ONE));
    }

    @Test
    void everyOperationToldIsHeldAtARowWhateverTheTypeHolds() {
        RowsComputed rows = RowsComputed.ENDLESS.withOperations(
                new Operations(List.of(between(0, 5)), Told.EVERY));
        assertTrue(computedAt(rows, 3));
        assertFalse(computedAt(rows, 6));
        assertFalse(rows.nothingStopsARow());
    }
}
