package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A congruence is solved by residues, and a residue against a modulus needs the modulus as a number.
 * A generator of astronomically many digits is a modulus this host holds no place for, and what
 * that comes to is an answer — every residue is possible, which is the widest progression — and not
 * an exception that stops the compile over a number the model never wrote down.
 */
class AModulusTheHostHoldsNoPlaceForWidensWhatIsSaidTest {

    /** Two to the power of a number of bits past what any host holds. */
    private static ExactRatio hugeWhole() {
        return new ExactRatio(BigInteger.ONE, BigInteger.ONE, (long) Integer.MAX_VALUE + 1, 0);
    }

    @Test
    void aWholeNumberSmallEnoughIsHeldAsItsDigits() {
        assertEquals(ExactAnswer.held(BigInteger.valueOf(1200)), ExactRatio.of(1200).wholeNumber());
        assertEquals(ExactAnswer.held(BigInteger.valueOf(1200)),
                new ExactRatio(BigInteger.valueOf(3), BigInteger.ONE, 4, 2).wholeNumber(),
                "written through its powers of two and five");
    }

    @Test
    void aWholeNumberOfMoreDigitsThanAHostHoldsIsAnAnswerAndNotAnException() {
        assertEquals(ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS),
                hugeWhole().wholeNumber());
    }

    @Test
    void aNumberThatIsNotWholeIsACallersMistake() {
        assertThrows(IllegalArgumentException.class,
                () -> new ExactRatio(BigInteger.ONE, BigInteger.valueOf(3)).wholeNumber());
    }

    /** {@code x ≡ 0 (mod 2^2147483648)} over positions that step. */
    @Test
    void aGeneratorTooLargeToWriteLeavesTheWidestProgressionOverWholeNumbers() {
        AdditiveImage image = new AdditiveImage.OverWholeNumbers(hugeWhole());

        AffinePreimage answer = image.affinePreimage(
                ExactRatio.ONE, ExactRatio.ZERO, Granularity.DISCRETE);

        AffinePreimage.Stepping every = assertInstanceOf(AffinePreimage.Stepping.class, answer);
        assertEquals(ExactRatio.ZERO, every.from());
        assertEquals(ExactRatio.ONE, every.by());
        assertEquals(Granularity.DISCRETE, every.spacing());
    }
}
