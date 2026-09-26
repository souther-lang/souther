package souther.exact;

import java.math.BigDecimal;
import java.math.BigInteger;

/**
 * What a {@code BigDecimal} holds of a number, apart from the scale it happens to be written at.
 *
 * <p>A {@code BigDecimal} is a number and a scale, and its operations answer for both: a product
 * asks for the sum of its factors' scales, and stripping the zeros asks for one scale less each
 * time. Either can leave the range of an {@code int} while the number it stands for is one the
 * type holds at another scale — {@code 10 × 10^-2147483647} is {@code 1 × 10^-2147483646}, and both
 * are numbers of scale near the floor. A reader that asks about the number and not about how it was
 * written must not be refused for the representation, so what is here answers the number.
 *
 * <p>Target-neutral: the compiler reasons with the same numbers the run time computes.
 */
public final class ExactDecimals {

    private ExactDecimals() {}

    /**
     * The amount {@code d} is, carried by as few digits as a {@code BigDecimal} can carry it: one
     * form for every value the language calls equal, which is what a hash of an amount and a
     * boundary's canonical number are both taken from.
     *
     * <p>{@code stripTrailingZeros} is that, until the scale it would need is one the type cannot
     * say: a scale is an {@code int}, and taking the zero off {@code (10, MIN_VALUE)} asks for
     * {@code MIN_VALUE - 1}, which it answers by throwing. Stopping at the floor instead still leaves
     * one form per amount — {@code (10, MIN_VALUE)} and {@code (100, MIN_VALUE + 1)} are one amount
     * and both stop at {@code (10, MIN_VALUE)} — because fixing the scale fixes the digits.
     */
    public static BigDecimal leastDigits(BigDecimal d) {
        if (d.signum() == 0) {
            return BigDecimal.ZERO;                  // every way of writing nothing is one amount
        }
        long room = (long) d.scale() - Integer.MIN_VALUE;
        if (room >= d.precision()) {
            return d.stripTrailingZeros();           // fewer zeros than digits: it cannot fall out
        }
        BigInteger digits = d.unscaledValue();
        int scale = d.scale();
        for (long left = room; left > 0; left--) {
            BigInteger[] divided = digits.divideAndRemainder(BigInteger.TEN);
            if (divided[1].signum() != 0) {
                break;
            }
            digits = divided[0];
            scale--;
        }
        return new BigDecimal(digits, scale);
    }

    /**
     * The number {@code a} times {@code b}, at whatever scale holds it, or null where no scale does.
     *
     * <p>The scale of the product is the sum of the factors', and {@code BigDecimal.multiply} refuses
     * a nonzero product whose sum leaves the range even where the number is held at another scale:
     * {@code 10 × 10^-2147483647} times {@code 10^-1} is {@code 10^-2147483647}, which the type
     * holds. So the digits are multiplied here and the zeros a sum above the range asks for are
     * taken off them, and a number is refused only where none can be: its digits have no zero left
     * to give, or its scale is below the floor.
     *
     * <p>Nought is nought at every scale, so it answers before any scale is summed.
     */
    public static BigDecimal product(BigDecimal a, BigDecimal b) {
        BigInteger digits = a.unscaledValue().multiply(b.unscaledValue());
        if (digits.signum() == 0) {
            return BigDecimal.ZERO;
        }
        long scale = (long) a.scale() + b.scale();
        while (scale > Integer.MAX_VALUE) {
            BigInteger[] divided = digits.divideAndRemainder(BigInteger.TEN);
            if (divided[1].signum() != 0) {
                return null;
            }
            digits = divided[0];
            scale--;
        }
        return scale < Integer.MIN_VALUE ? null : new BigDecimal(digits, (int) scale);
    }
}
