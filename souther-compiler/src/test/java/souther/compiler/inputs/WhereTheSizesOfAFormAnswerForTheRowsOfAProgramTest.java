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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The sizes of a form's addends answer for the rows of a program only where they are the sizes the
 * program works its operations out over: the program adds the form up, or every operation it
 * works out is told and is a sum of the form's own terms.
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

    private static boolean answer(Operations operations) {
        return operations.theSizesOfTheFormAnswer(TERMS, ExactRatio.ZERO);
    }

    @Test
    void aProgramTakenToAddTheFormUpIsAnsweredByTheSizes() {
        assertTrue(answer(Operations.NONE));
    }

    @Test
    void aProgramWithNothingBeyondTheFormToStopItIsAnsweredByTheSizes() {
        assertTrue(answer(new Operations(List.of(), Told.EVERY)));
    }

    @Test
    void everyOperationBeingASumOfTheFormsTermsIsAnsweredByTheSizes() {
        assertTrue(answer(new Operations(List.of(sum(1, -1, 0)), Told.EVERY)));
    }

    @Test
    void anOperationThatIsNoSumOfTheFormIsNotAnsweredByTheSizes() {
        // `(a + 1) - 1 >= b` works out `a + 1`, which the form `a - b` does not.
        assertFalse(answer(new Operations(List.of(sum(1, 0, 1)), Told.EVERY)));
    }

    @Test
    void aProgramThatMayStopUntoldIsNotAnsweredByTheSizes() {
        assertFalse(answer(new Operations(List.of(sum(1, -1, 0)), Told.SOME)));
    }
}
