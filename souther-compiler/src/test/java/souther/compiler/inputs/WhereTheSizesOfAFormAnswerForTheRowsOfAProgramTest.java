package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.IntSum;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Term;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The sizes of a form's addends are asked two things of a program. Whether every row within them
 * is computed, which a row on each side of a relation is shown by: the program adds the form up,
 * or every operation it works out is told and is a sum of some of the form's terms. And whether
 * every row computed is within them, which a value settled by the rows that are is told by: only
 * where nothing but the form can stop a row, since an operation's rows are its own and the sizes
 * count a constant the program may only compare with, and leave out the least value of the type,
 * which a sum of terms weighed one is worked out at.
 */
class WhereTheSizesOfAFormAnswerForTheRowsOfAProgramTest {

    private static final BigInteger LEAST = BigInteger.valueOf(Long.MIN_VALUE);
    private static final BigInteger GREATEST = BigInteger.valueOf(Long.MAX_VALUE);

    /** {@code a - b}, each weighed by one and nought. */
    private static final List<Term<String>> TERMS = List.of(term("a", 1), term("b", -1));

    private static Term<String> term(String place, long weight) {
        return new Term<>(List.of(place), ExactRatio.of(weight), NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, null, true,
                Granularity.DISCRETE, NumericDomain.Bounds.OPEN, place);
    }

    private static IntSum sum(long aWeight, long bWeight, long constant) {
        return new IntSum(Map.of("a", ExactRatio.of(aWeight), "b", ExactRatio.of(bWeight)),
                ExactRatio.of(constant), LEAST, GREATEST);
    }

    private static boolean within(Operations operations) {
        return operations.theSizesAreRowsComputed(TERMS, ExactRatio.ZERO);
    }

    @Test
    void aProgramTakenToAddTheFormUpHasEveryRowWithinTheSizesComputed() {
        assertTrue(within(Operations.NONE));
    }

    @Test
    void aProgramWithNothingBeyondTheFormToStopItHasEveryRowWithinTheSizesComputed() {
        assertTrue(within(new Operations(List.of(), Told.EVERY)));
    }

    @Test
    void everyOperationBeingASumOfTheFormsTermsHasEveryRowWithinTheSizesComputed() {
        assertTrue(within(new Operations(List.of(sum(1, -1, 0)), Told.EVERY)));
    }

    @Test
    void anOperationThatIsNoSumOfTheFormLeavesRowsWithinTheSizesUncomputed() {
        // `(a + 1) - 1 >= b` works out `a + 1`, which the form `a - b` does not.
        assertFalse(within(new Operations(List.of(sum(1, 0, 1)), Told.EVERY)));
    }

    @Test
    void aProgramThatMayStopUntoldLeavesRowsWithinTheSizesUncomputed() {
        assertFalse(within(new Operations(List.of(sum(1, -1, 0)), Told.SOME)));
    }

    @Test
    void everyRowComputedIsWithinTheSizesOnlyWhereNothingButTheFormCanStopOne() {
        assertTrue(Operations.NONE.theSizesAreEveryRowComputed());
        assertTrue(new Operations(List.of(), Told.EVERY).theSizesAreEveryRowComputed());
    }

    @Test
    void anOperationComputesRowsBeyondTheSizesEvenWhereItIsTheFormItself() {
        // `a - b >= 2` works out `a - b` and compares it with 2, which the form `a - b - 2`
        // counts as an addend; and `a + b >= 0` is worked out at `b` the type's least, which
        // the sizes leave out.
        assertFalse(new Operations(List.of(sum(1, -1, 0)), Told.EVERY)
                .theSizesAreEveryRowComputed());
        assertFalse(new Operations(List.of(sum(1, 1, 0)), Told.EVERY)
                .theSizesAreEveryRowComputed());
        assertFalse(new Operations(List.of(sum(1, -1, 0)), Told.SOME)
                .theSizesAreEveryRowComputed());
    }

    @Test
    void theSizesStopNowhereWhereNoOperationIsToldOfAnEveryOneTold() {
        assertNull(new Operations(List.of(), Told.EVERY).sizesStopAt(GREATEST));
        assertEquals(GREATEST, Operations.NONE.sizesStopAt(GREATEST));
    }
}
