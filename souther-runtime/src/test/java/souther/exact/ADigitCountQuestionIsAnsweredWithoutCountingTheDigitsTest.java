package souther.exact;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Whether a decimal has at most so many digits, and the two answers built on it, agree with the
 * digit count itself at the edges: one digit either side of a power of ten, the numbers a bit length
 * alone settles, a thousand digits and one past, and scales across the whole of an int.
 */
class ADigitCountQuestionIsAnsweredWithoutCountingTheDigitsTest {

    private static final int[] SCALES = {Integer.MIN_VALUE, Integer.MIN_VALUE + 1, -1001, -1000, -999,
                                         -5, -1, 0, 1, 5, 998, 999, 1000, 1001, Integer.MAX_VALUE - 1,
                                         Integer.MAX_VALUE};

    @Test
    void hasAtMostDigitsIsTheDigitCountComparedWithTheLimit() {
        List<String> differ = new ArrayList<>();
        for (BigInteger unscaled : unscaledValues()) {
            BigDecimal d = new BigDecimal(unscaled);
            for (long limit : new long[] {0, 1, 2, 3, 4, 9, 10, 999, 1000, 1001}) {
                boolean expected = d.precision() <= limit;
                if (ExactDecimals.hasAtMostDigits(d, limit) != expected) {
                    differ.add(unscaled.bitLength() + " bits, limit " + limit);
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    @Test
    void fitsPlainNotationIsTheLengthComparedWithTheLimit() {
        List<String> differ = new ArrayList<>();
        for (BigInteger unscaled : unscaledValues()) {
            for (int scale : SCALES) {
                BigDecimal d = new BigDecimal(unscaled, scale);
                boolean expected = ExactDecimals.plainNotationLength(d) <= ExactDecimals.MAX_SPELT_OUT_DIGITS;
                if (ExactDecimals.fitsPlainNotation(d) != expected) {
                    differ.add(unscaled.bitLength() + " bits at " + scale);
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    @Test
    void leastDigitsIsOneFormPerAmount() {
        List<String> differ = new ArrayList<>();
        for (BigInteger unscaled : unscaledValues()) {
            for (int scale : SCALES) {
                BigDecimal d = new BigDecimal(unscaled, scale);
                BigDecimal least = ExactDecimals.leastDigits(d);
                boolean sameAmount = d.signum() == 0 || least.compareTo(d) == 0;
                if (!sameAmount || !least.equals(ExactDecimals.leastDigits(least))) {
                    differ.add(unscaled.bitLength() + " bits at " + scale);
                }
                if (scale > Integer.MIN_VALUE + 2000 && d.signum() != 0 && !least.equals(d.stripTrailingZeros())) {
                    differ.add("not stripped: " + unscaled.bitLength() + " bits at " + scale);
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    @Test
    void leastDigitsStopsAtTheFloorWhateverNumberOfZerosItMeets() {
        List<String> differ = new ArrayList<>();
        for (int zeros : new int[] {0, 1, 2, 9, 10, 11, 100, 999, 1000, 1001}) {
            for (long odd : new long[] {1, 7, -7, 25, 3}) {
                BigInteger unscaled = BigInteger.TEN.pow(zeros).multiply(BigInteger.valueOf(odd));
                for (int offset : new int[] {0, 1, zeros - 1, zeros, zeros + 1, zeros + 2, 5000}) {
                    if (offset < 0) {
                        continue;
                    }
                    BigDecimal d = new BigDecimal(unscaled, Integer.MIN_VALUE + offset);
                    BigDecimal expected = oneZeroAtATime(unscaled, Integer.MIN_VALUE + offset);
                    BigDecimal asked = ExactDecimals.leastDigits(d);
                    if (!asked.equals(expected)) {
                        differ.add(odd + "e" + zeros + " at floor + " + offset);
                    }
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    private static BigDecimal oneZeroAtATime(BigInteger unscaled, int scale) {
        BigInteger digits = unscaled;
        int at = scale;
        while (at > Integer.MIN_VALUE) {
            BigInteger[] divided = digits.divideAndRemainder(BigInteger.TEN);
            if (divided[1].signum() != 0) {
                break;
            }
            digits = divided[0];
            at--;
        }
        return new BigDecimal(digits, at);
    }

    private static List<BigInteger> unscaledValues() {
        List<BigInteger> out = new ArrayList<>();
        for (int digits : new int[] {1, 2, 3, 4, 5, 18, 19, 20, 998, 999, 1000, 1001, 1002}) {
            BigInteger power = BigInteger.TEN.pow(digits - 1);
            for (BigInteger each : new BigInteger[] {
                    power, power.add(BigInteger.ONE), power.multiply(BigInteger.TEN).subtract(BigInteger.ONE),
                    power.multiply(BigInteger.TEN)}) {
                out.add(each);
                out.add(each.negate());
            }
        }
        for (int bits : new int[] {1, 2, 3, 4, 3000, 3001, 4000, 4001}) {
            BigInteger power = BigInteger.ONE.shiftLeft(bits);
            for (BigInteger each : new BigInteger[] {power, power.subtract(BigInteger.ONE)}) {
                out.add(each);
                out.add(each.negate());
            }
        }
        out.add(BigInteger.ZERO);
        out.add(BigInteger.ONE.shiftLeft(100_000).subtract(BigInteger.valueOf(3)));
        out.add(BigInteger.ONE.shiftLeft(100_000).subtract(BigInteger.valueOf(3)).negate());
        return out;
    }
}
