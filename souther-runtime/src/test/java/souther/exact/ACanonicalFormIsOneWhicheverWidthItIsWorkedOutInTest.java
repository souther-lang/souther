package souther.exact;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A value small enough for longs is brought to its canonical form in longs, and the form is the one
 * the whole numbers come to: the same parts as reducing the fraction, taking the twos and taking the
 * fives one at a time, written here over {@code BigInteger} alone and held as the answer.
 *
 * <p>Asked over the values at the edge of the longs as well as ordinary ones: both signs, the
 * largest magnitudes that take the narrow way and the smallest that do not, and fractions carrying
 * twos, fives and a common factor on both sides.
 */
class ACanonicalFormIsOneWhicheverWidthItIsWorkedOutInTest {

    @Test
    void everyValueComesToTheFormItsWholeNumbersSay() {
        List<BigInteger> wholes = new ArrayList<>();
        for (long each : new long[] {1, 2, 3, 5, 7, 10, 20, 25, 40, 125, 1000, 1024, 3125, 6250,
                                     999_999_937L, (1L << 61), (1L << 62) - 1, (1L << 62),
                                     (1L << 62) + 1, Long.MAX_VALUE, 5_000_000_000_000_000_000L}) {
            wholes.add(BigInteger.valueOf(each));
            wholes.add(BigInteger.valueOf(each).negate());
        }
        wholes.add(BigInteger.valueOf(Long.MIN_VALUE));
        wholes.add(BigInteger.ONE.shiftLeft(64).multiply(BigInteger.valueOf(15)));
        Random random = new Random(20261003L);
        for (int i = 0; i < 150; i++) {
            BigInteger factor = BigInteger.valueOf(2).pow(random.nextInt(8))
                    .multiply(BigInteger.valueOf(5).pow(random.nextInt(6)));
            wholes.add(BigInteger.valueOf(random.nextLong() >> random.nextInt(63)).multiply(factor));
        }
        List<String> differ = new ArrayList<>();
        for (BigInteger numerator : wholes) {
            for (BigInteger denominator : wholes) {
                if (denominator.signum() == 0) {
                    continue;
                }
                ExactParts asked = ExactArithmetic.canonical(numerator, denominator, 3, -4);
                ExactParts expected = reduced(numerator, denominator, 3, -4);
                if (!asked.equals(expected)) {
                    differ.add(numerator + "/" + denominator + ": " + asked + " != " + expected);
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    @Test
    void anExponentPastSixtyFourBitsIsRefusedInLongsAsItIsWide() {
        assertThrows(ExactRangeExceeded.class, () -> ExactArithmetic.canonical(
                BigInteger.TWO, BigInteger.ONE, Long.MAX_VALUE, 0));
        assertThrows(ExactRangeExceeded.class, () -> ExactArithmetic.canonical(
                BigInteger.ONE, BigInteger.valueOf(5), 0, Long.MIN_VALUE));
    }

    /** The canonical form worked out the plain way, one factor at a time. */
    private static ExactParts reduced(BigInteger numerator, BigInteger denominator, long twos,
                                      long fives) {
        if (numerator.signum() == 0) {
            return ExactParts.ZERO;
        }
        if (denominator.signum() < 0) {
            numerator = numerator.negate();
            denominator = denominator.negate();
        }
        BigInteger common = numerator.gcd(denominator);
        numerator = numerator.divide(common);
        denominator = denominator.divide(common);
        BigInteger two = BigInteger.TWO;
        BigInteger five = BigInteger.valueOf(5);
        while (numerator.mod(two).signum() == 0) {
            numerator = numerator.divide(two);
            twos++;
        }
        while (denominator.mod(two).signum() == 0) {
            denominator = denominator.divide(two);
            twos--;
        }
        while (numerator.mod(five).signum() == 0) {
            numerator = numerator.divide(five);
            fives++;
        }
        while (denominator.mod(five).signum() == 0) {
            denominator = denominator.divide(five);
            fives--;
        }
        return new ExactParts(numerator, denominator, twos, fives);
    }
}
