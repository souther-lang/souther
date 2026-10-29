package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.math.BigInteger;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The witness that puts a remainder's form through every remainder is one at which the run gets
 * past every operation it works out, asked of the operations and not of the form they sum to.
 */
class ARunGetsPastTheOperationsAtTheWitnessOfARemainderTest {

    private static final BigInteger LEAST = BigInteger.valueOf(Long.MIN_VALUE);
    private static final BigInteger GREATEST = BigInteger.valueOf(Long.MAX_VALUE);
    private static final BigInteger TOP = BigInteger.TEN;

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("a"));
    private static final NumericTerm Y = new NumericTerm.ValueOf(TermPath.of("y"));
    private static final Set<NumericTerm> FORM = Set.of(X, A);

    private static UndividedByARelation.IntOperation over(
            LinearForm<NumericTerm> form) {
        return new UndividedByARelation.IntOperation(form, LEAST, GREATEST, List.of());
    }

    private static LinearForm<NumericTerm> weighing(NumericTerm number, long weight,
                                                    long constant) {
        return LinearForm.weighing(number, ExactRatio.of(weight))
                .plus(LinearForm.constant(ExactRatio.of(constant))).orNull();
    }

    /** The run gets past an operation over none of the numbers of the form only where
     *  {@code apartIsGotPast}. */
    private static boolean getsPast(boolean apartIsGotPast,
                                    UndividedByARelation.IntOperation... operations) {
        return UndividedByARelation.getsPastAtTheWitness(List.of(operations), FORM, X, TOP,
                each -> apartIsGotPast);
    }

    private static boolean getsPast(UndividedByARelation.IntOperation... operations) {
        return getsPast(false, operations);
    }

    @Test
    void anOperationOverTheWitnessIsAskedAtBothEndsOfTheWindow() {
        assertTrue(getsPast(over(weighing(X, 3, 5))));
        assertFalse(getsPast(over(weighing(X, 3, Long.MAX_VALUE))));
        assertFalse(getsPast(over(weighing(X, Long.MAX_VALUE, 0))));
    }

    @Test
    void anOperationOverNoNumberOfTheFormIsGotPastOnlyWhereTheRunIsShownToGetPastIt() {
        // The product of the greatest Int and y stops the run for every y but nought, whatever
        // the form comes to once it is cancelled against another of the same.
        UndividedByARelation.IntOperation product = over(weighing(Y, Long.MAX_VALUE, 0));
        UndividedByARelation.IntOperation shift = over(weighing(X, 3, 5));
        assertTrue(getsPast(true, shift, product));
        assertFalse(getsPast(false, shift, product));
        assertFalse(getsPast(shift, product));
    }

    @Test
    void anOperationOverANumberOfTheFormAndOneItDoesNotHaveIsGivenUp() {
        LinearForm<NumericTerm> mixed = weighing(X, 1, 0)
                .plus(LinearForm.weighing(Y, ExactRatio.of(1))).orNull();
        assertFalse(getsPast(over(mixed)));
        assertFalse(getsPast(over(weighing(X, 1, 0)), over(mixed)));
    }

    @Test
    void anotherNumberOfTheFormStandsAtNought() {
        LinearForm<NumericTerm> both = weighing(X, 1, 5)
                .plus(LinearForm.weighing(A, ExactRatio.of(Long.MAX_VALUE))).orNull();
        assertTrue(getsPast(over(both)));
    }
}
