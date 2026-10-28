package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.IntSum;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The sizes of a form's addends answer for the rows of a program only where nothing but the form
 * can stop a row: the program is taken to add the form up, or every operation it works out is
 * told and there is none. Where an operation is told, it is the rows it computes that count, and
 * the sizes are a bound of them that counts a constant the program may only compare with, and
 * leaves out the least value of the type, which a sum of terms weighed one is worked out at.
 */
class WhereTheSizesOfAFormAnswerForTheRowsOfAProgramTest {

    private static final BigInteger LEAST = BigInteger.valueOf(Long.MIN_VALUE);
    private static final BigInteger GREATEST = BigInteger.valueOf(Long.MAX_VALUE);

    private static IntSum sum(long aWeight, long bWeight, long constant) {
        return new IntSum(Map.of("a", ExactRatio.of(aWeight), "b", ExactRatio.of(bWeight)),
                ExactRatio.of(constant), LEAST, GREATEST);
    }

    @Test
    void aProgramTakenToAddTheFormUpIsAnsweredByTheSizes() {
        assertTrue(Operations.NONE.theSizesOfTheFormAnswer());
    }

    @Test
    void aProgramWithNothingBeyondTheFormToStopItIsAnsweredByTheSizes() {
        assertTrue(new Operations(List.of(), Told.EVERY).theSizesOfTheFormAnswer());
    }

    @Test
    void anOperationIsNotAnsweredByTheSizesEvenWhereItIsTheFormItself() {
        // `a - b >= 2` works out `a - b` and compares it with 2, which the form `a - b - 2`
        // counts as an addend; and `a + b >= 0` is worked out at `b` the type's least, which
        // the sizes leave out.
        assertFalse(new Operations(List.of(sum(1, -1, 0)), Told.EVERY).theSizesOfTheFormAnswer());
        assertFalse(new Operations(List.of(sum(1, 1, 0)), Told.EVERY).theSizesOfTheFormAnswer());
    }

    @Test
    void aProgramThatMayStopUntoldIsNotAnsweredByTheSizes() {
        assertFalse(new Operations(List.of(sum(1, -1, 0)), Told.SOME).theSizesOfTheFormAnswer());
    }

    @Test
    void theSizesStopNowhereWhereNoOperationIsToldOfAnEveryOneTold() {
        assertNull(new Operations(List.of(), Told.EVERY).sizesStopAt(GREATEST));
        assertEquals(GREATEST, Operations.NONE.sizesStopAt(GREATEST));
    }
}
