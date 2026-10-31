package souther.exact;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The canonical form of a decimal is the one of its unscaled value and its negated scale, whichever
 * way the decimal is read: whether a long holds the unscaled value decides only the width the work is
 * done in.
 *
 * <p>Asked where the digit count and the width part: a nineteen-digit number a long holds, the
 * greatest and the least long, the first numbers past either end, and a number of a million bits.
 * Each is asked at scales across the whole of an int, the least and the greatest included.
 */
class ADecimalIsReadAsALongWhereALongHoldsItsUnscaledValueTest {

    private static final int[] SCALES = {Integer.MIN_VALUE, Integer.MIN_VALUE + 1, -1, 0, 1,
                                         Integer.MAX_VALUE - 1, Integer.MAX_VALUE};

    @Test
    void theFormOfADecimalIsTheOneOfItsUnscaledValueAndScale() {
        List<String> differ = new ArrayList<>();
        for (BigInteger unscaled : unscaledValues()) {
            for (int scale : SCALES) {
                ExactParts asked = ExactArithmetic.canonical(new BigDecimal(unscaled, scale));
                ExactParts expected = ExactArithmetic.canonical(
                        unscaled, BigInteger.ONE, -(long) scale, -(long) scale);
                if (!asked.equals(expected)) {
                    differ.add(unscaled + " at " + scale + ": " + asked + " != " + expected);
                }
            }
        }
        assertEquals(List.of(), differ.subList(0, Math.min(differ.size(), 5)));
    }

    private static List<BigInteger> unscaledValues() {
        List<BigInteger> out = new ArrayList<>();
        BigInteger greatest = BigInteger.valueOf(Long.MAX_VALUE);
        BigInteger least = BigInteger.valueOf(Long.MIN_VALUE);
        for (BigInteger each : new BigInteger[] {
                BigInteger.ZERO, BigInteger.ONE, BigInteger.TEN.pow(17), BigInteger.TEN.pow(18),
                greatest, greatest.add(BigInteger.ONE), greatest.subtract(BigInteger.ONE),
                least, least.add(BigInteger.ONE), least.subtract(BigInteger.ONE),
                BigInteger.ONE.shiftLeft(1_000_000).subtract(BigInteger.valueOf(3))}) {
            out.add(each);
            out.add(each.negate());
        }
        return out;
    }
}
