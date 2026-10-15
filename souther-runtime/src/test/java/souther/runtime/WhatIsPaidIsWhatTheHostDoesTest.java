package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a number's operation is paid for is the work the host does, and a scale costs nothing where
 * nothing is built at it.
 *
 * <p>Each pair here holds values a few words long at scales a million apart. The host settles them
 * by a nought, a sign or where their first digits stand, and builds nothing at the scale; a count
 * worked out from the scale would charge for a power of ten a million digits long that nobody makes.
 * The last case is the other side: a sum whose answer really is that long is paid for as that long.
 */
class WhatIsPaidIsWhatTheHostDoesTest {

    private static final int FAR = 1_000_000;

    /** As much as reading and comparing a few words may cost, and far less than a power of ten a
     *  million digits long. */
    private static final long A_FEW_WORDS = 1_000;

    private static final class Counting implements WorkCheckpoint {
        long paid;

        @Override
        public void spend(long pieces) {
            paid += pieces;
        }
    }

    private static long paidFor(java.util.function.Consumer<WorkCheckpoint> operation) {
        Counting counting = new Counting();
        operation.accept(counting);
        return counting.paid;
    }

    private static final BigDecimal ZERO_FAR = new BigDecimal(BigInteger.ZERO, FAR);
    private static final BigDecimal ONE_FAR = new BigDecimal(BigInteger.ONE, FAR);
    private static final BigDecimal ONE_FAR_UP = new BigDecimal(BigInteger.ONE, -FAR);

    @Test
    void aComparisonSettledByANoughtASignOrAPlaceCostsItsWords() {
        assertTrue(paidFor(c -> DecimalMath.compare(ZERO_FAR, BigDecimal.ZERO, c)) < A_FEW_WORDS);
        assertTrue(paidFor(c -> DecimalMath.compare(ONE_FAR, BigDecimal.ONE.negate(), c)) < A_FEW_WORDS);
        assertTrue(paidFor(c -> DecimalMath.compare(ONE_FAR, BigDecimal.ONE, c)) < A_FEW_WORDS);
        assertTrue(paidFor(c -> Values.equal(ONE_FAR, BigDecimal.ONE, c)) < A_FEW_WORDS);
    }

    @Test
    void aNoughtBroughtToAnotherScaleCostsItsWords() {
        assertTrue(paidFor(c -> DecimalMath.add(new BigDecimal(BigInteger.ZERO, -FAR), BigDecimal.ONE, c))
                < A_FEW_WORDS);
        assertTrue(paidFor(c -> DecimalMath.round(FAR, new HALF_UP(), BigDecimal.ZERO, c)) < A_FEW_WORDS);
        assertTrue(paidFor(c -> RationalMath.toDecimal(FAR, new HALF_UP(), Rational.ZERO, c)) < A_FEW_WORDS);
    }

    @Test
    void aRationalComparisonSettledByItsSignCostsItsWords() {
        Rational tiny = Rational.of(ONE_FAR);
        assertTrue(paidFor(c -> RationalMath.compare(tiny, Rational.of(-1), c)) < A_FEW_WORDS);
        assertTrue(paidFor(c -> RationalMath.compare(tiny, tiny, c)) < A_FEW_WORDS);
    }

    /** A sum whose answer is a million digits long is paid for as that long. */
    @Test
    void aSumThatIsBuiltAtTheFarScaleIsPaidForAsLongAsItIs() {
        long paid = paidFor(c -> DecimalMath.add(ONE_FAR_UP, BigDecimal.ONE, c));
        assertTrue(paid > (long) FAR / 20, "a sum a million digits long was paid " + paid);
    }
}
