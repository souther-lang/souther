package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.DecimalOperation.Formed;
import souther.compiler.inputs.DecimalOperation.Worked;
import souther.compiler.inputs.DecimalOperation.Written;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.BinOp;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a program gets past a decimal operation is what the run time says of the operation on
 * the row's own values, and not a region of the numbers its operands come to: nought written at
 * the scale of the greatest {@code int} is the number nought, and its product with four has no
 * room.
 */
class ADecimalOperationIsAskedByWorkingItOutOnARowTest {

    private static final BigDecimal FOUR = new BigDecimal("4.0");
    private static final BigDecimal NOUGHT_AT_THE_FLOOR =
            new BigDecimal(BigInteger.ZERO, Integer.MAX_VALUE);

    /** {@code h * 4.0}, with {@code h} the number the key {@code "h"} stands at. */
    private static final DecimalOperation TIMES_FOUR = new DecimalOperation(BinOp.MUL,
            List.of(new Formed(Map.of("h", ExactRatio.ONE), ExactRatio.ZERO), new Written(FOUR)),
            List.of());

    private static boolean completesAt(ExactRatio h, DecimalOperation... operations) {
        return DecimalOperation.allCompleteAt(List.of(operations), Map.of("h", h));
    }

    @Test
    void aProductOfANumberARowHasIsWorkedOut() {
        assertTrue(completesAt(ExactRatio.of(42), TIMES_FOUR));
    }

    @Test
    void aNumberNoDecimalWritesIsNoRow() {
        ExactRatio aThird = ExactRatio.ONE.dividedBy(ExactRatio.of(3)).orNull();
        assertFalse(completesAt(aThird, TIMES_FOUR));
    }

    @Test
    void aNumberWrittenAtMorePlacesThanARowIsBuiltAtIsNoRowOfThoseBuilt() {
        ExactRatio tiny = ExactRatio.of(new BigDecimal(BigInteger.ONE,
                DecimalOperation.PLACES_A_ROW_IS_BUILT_AT + 1));
        ExactRatio atTheLimit = ExactRatio.of(new BigDecimal(BigInteger.ONE,
                DecimalOperation.PLACES_A_ROW_IS_BUILT_AT));
        assertFalse(completesAt(tiny, TIMES_FOUR));
        assertTrue(completesAt(atTheLimit, TIMES_FOUR));
    }

    @Test
    void aTermTheRowDoesNotNameIsNoRow() {
        assertFalse(DecimalOperation.allCompleteAt(List.of(TIMES_FOUR), Map.of("s", ExactRatio.ONE)));
    }

    @Test
    void theSameNumberWrittenAtAnotherScaleIsWorkedOutOrNotAsTheRunTimeSays() {
        DecimalOperation written = new DecimalOperation(BinOp.MUL,
                List.of(new Written(BigDecimal.ZERO), new Written(FOUR)), List.of());
        DecimalOperation writtenAtTheFloor = new DecimalOperation(BinOp.MUL,
                List.of(new Written(NOUGHT_AT_THE_FLOOR), new Written(FOUR)), List.of());
        assertEquals(0, BigDecimal.ZERO.compareTo(NOUGHT_AT_THE_FLOOR));
        assertTrue(completesAt(ExactRatio.ZERO, written));
        assertFalse(completesAt(ExactRatio.ZERO, writtenAtTheFloor));
    }

    @Test
    void anOperationIsWorkedOutOnTheScaleTheOneBeforeItLeft() {
        BigDecimal wide = new BigDecimal(BigInteger.ZERO, 1_000_000_000);
        DecimalOperation first = new DecimalOperation(BinOp.MUL,
                List.of(new Written(wide), new Written(wide)), List.of());
        DecimalOperation then = new DecimalOperation(BinOp.MUL,
                List.of(new Worked(0), new Written(new BigDecimal(BigInteger.ZERO, 200_000_000))),
                List.of(0));
        assertTrue(completesAt(ExactRatio.ZERO, first));
        assertFalse(completesAt(ExactRatio.ZERO, first, then));
    }

    @Test
    void aRowIsComputedWhereEveryOperationToldIsWorkedOutAndNowhereElse() {
        Operations told = new Operations(List.of(), List.of(TIMES_FOUR), Told.EVERY);
        RowsComputed rows = RowsComputed.upTo(null).withOperations(told);
        assertTrue(rows.mayStopARow());
        assertTrue(rows.computedAt(() -> Map.of("h", ExactRatio.of(42))));
        assertFalse(rows.computedAt(() -> Map.of()));
        Operations someToldOnly = new Operations(List.of(), List.of(TIMES_FOUR), Told.SOME);
        assertFalse(RowsComputed.upTo(null).withOperations(someToldOnly)
                .computedAt(() -> Map.of("h", ExactRatio.of(42))));
    }
}
