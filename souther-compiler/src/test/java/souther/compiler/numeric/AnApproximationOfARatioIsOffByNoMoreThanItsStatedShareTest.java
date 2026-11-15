package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a ratio is as a {@code double} ({@link ExactRatio#approximately}) is its value to within
 * {@link ExactRatio#APPROXIMATELY_OFF}, or it is not a number.
 *
 * <p>The premise tree passes premises over by arithmetic on these and allows for that much error and
 * no more, so this is the one claim its soundness rests on at the number's side. It is held over
 * ratios drawn the way their parts are: a fraction of wide whole numbers, times a power of two and a
 * power of five each, so that a step of the working-out can overflow, fall below the smallest normal
 * number and come back, or lose its digits at either end, and the result still be a number a
 * {@code double} holds.
 */
class AnApproximationOfARatioIsOffByNoMoreThanItsStatedShareTest {

    private static ExactRatio ratio(BigInteger numerator, BigInteger denominator, int twos,
                                    int fives) {
        ExactRatio value = ExactRatio.of(numerator, denominator);
        value = by(value, BigInteger.TWO.pow(Math.abs(twos)), twos);
        return by(value, BigInteger.valueOf(5).pow(Math.abs(fives)), fives);
    }

    private static ExactRatio by(ExactRatio value, BigInteger power, int exponent) {
        ExactRatio factor = ExactRatio.of(power);
        return (exponent >= 0 ? value.times(factor) : value.dividedBy(factor)).orNull();
    }

    private static void assertOffByNoMoreThanItsShare(ExactRatio exact) {
        double near = exact.approximately();
        if (Double.isNaN(near)) {
            return;
        }
        ExactRatio off = exact.minus(ExactRatio.of(new BigDecimal(near))).orNull();
        ExactRatio allowed = exact.abs().times(
                ExactRatio.of(BigDecimal.valueOf(ExactRatio.APPROXIMATELY_OFF))).orNull();
        assertTrue(off != null && allowed != null, "the error of " + exact + " could not be read");
        assertTrue(off.abs().compareTo(allowed) <= 0,
                exact + " is " + near + " as a double, off by more than "
                        + ExactRatio.APPROXIMATELY_OFF + " of it");
    }

    @Test
    void aRatioOfAnySizeIsOffByNoMoreThanTheShareOrIsNotANumber() {
        Random random = new Random(3);
        int numbers = 0;
        for (int each = 0; each < 6000; each++) {
            BigInteger numerator = new BigInteger(1 + random.nextInt(420), random).add(BigInteger.ONE);
            BigInteger denominator = new BigInteger(1 + random.nextInt(420), random)
                    .add(BigInteger.ONE);
            ExactRatio ratio = ratio(numerator, denominator, random.nextInt(2201) - 1100,
                    random.nextInt(661) - 330);
            if (random.nextBoolean()) {
                ratio = ratio.negated();
            }
            assertOffByNoMoreThanItsShare(ratio);
            if (!Double.isNaN(ratio.approximately())) {
                numbers++;
            }
        }
        assertTrue(numbers > 500, "only " + numbers + " of the ratios were a number to hold");
    }

    @Test
    void aRatioWhoseWorkingOutPassesBelowTheSmallestNormalNumberIsNotANumber() {
        ExactRatio scaledDown = ratio(BigInteger.ONE, new BigInteger("1000000000039"), -1000, 300);
        assertTrue(Double.isNaN(scaledDown.approximately()),
                "five to the 300 over two to the 1000 is held below the smallest normal number "
                        + "along the way");
        ExactRatio smallFirst = ratio(BigInteger.ONE, BigInteger.TEN.pow(308).add(BigInteger.ONE),
                1000, 0);
        assertOffByNoMoreThanItsShare(smallFirst);
    }

    @Test
    void theWindowOfSizesIsFromTwoToTheMinus200ToTwoToThe200() {
        assertEquals(BigInteger.TWO.pow(199).doubleValue(),
                ExactRatio.of(BigInteger.TWO.pow(199)).approximately());
        assertTrue(Double.isNaN(ExactRatio.of(BigInteger.TWO.pow(201)).approximately()));
        assertTrue(Double.isNaN(ratio(BigInteger.ONE, BigInteger.ONE, -201, 0).approximately()));
        assertTrue(ratio(BigInteger.ONE, BigInteger.ONE, -199, 0).approximately() > 0);
        assertEquals(0.0, ExactRatio.ZERO.approximately());
        assertTrue(Double.isNaN(ExactRatio.tenTo(Long.MIN_VALUE).approximately()));
        assertTrue(Double.isNaN(ExactRatio.tenTo(Long.MAX_VALUE).approximately()));
    }
}
