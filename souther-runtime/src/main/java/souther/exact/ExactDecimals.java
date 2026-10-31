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
     * How many digits a plain notation may be spelt out into. It bounds the <em>expansion</em> and
     * not the output: a value that already carries a thousand significant digits is written with
     * all of them, here as anywhere, and that is not this rule's business. What this stops is a
     * compact input asking for an enormous output — {@code 1E+1000000} is eleven characters and a
     * million and one digits.
     *
     * <p>A thousand is where a reader gives up as well ({@code jackson-core}'s
     * {@code StreamReadConstraints.DEFAULT_MAX_NUM_LEN}), which is where the figure comes from. It is
     * a reference point and not the definition: a caller past this compiler's own boundary is free
     * to hold its own limit.
     */
    public static final int MAX_SPELT_OUT_DIGITS = 1000;

    /**
     * The amount, written in plain notation where that is at most {@link #MAX_SPELT_OUT_DIGITS}
     * digits, or in exponent notation otherwise — {@code toString}'s own form, which switches to it
     * on the same terms {@code toPlainString} never does.
     *
     * <p>For a reader and not for identity: two forms of one amount are not asked to agree here, so
     * a caller after that reaches {@link #leastDigits} first, the way {@link #plainNotationLength}
     * already expects to be reached. What this is for is a diagnostic, a report or any other text a
     * person or a tool reads, where a compact number's plain notation would otherwise be a cost the
     * number itself never signalled.
     */
    public static String spelledBounded(BigDecimal d) {
        return fitsPlainNotation(d) ? d.toPlainString() : d.toString();
    }

    /**
     * Whether {@code d}'s plain notation is at most {@link #MAX_SPELT_OUT_DIGITS} digits, cheaply —
     * without building the notation to measure it.
     *
     * <p>The same answer as comparing {@link #plainNotationLength} with the limit, reached by asking
     * {@link #hasAtMostDigits} what that length asks of the digit count: the sign and the point, and
     * the zeros the scale stands for, are taken off the limit first.
     *
     * <p>For a caller with no exponent notation to fall back to: a grammar that writes a number only
     * in plain notation has nothing {@link #spelledBounded} can hand it past this count, and has to
     * answer with an amount's absence instead of the amount. {@link #spelledBounded} is this same
     * question asked by a caller that does have somewhere to fall back to.
     */
    public static boolean fitsPlainNotation(BigDecimal d) {
        long sign = d.signum() < 0 ? 1 : 0;
        long scale = d.scale();
        if (d.signum() == 0) {
            return scale <= 0 || 2 + scale <= MAX_SPELT_OUT_DIGITS;
        }
        if (scale <= 0) {
            return hasAtMostDigits(d, MAX_SPELT_OUT_DIGITS - sign + scale);
        }
        // With more digits than the scale the point falls among them and the length is the digits
        // and the point; with fewer, it is the leading zeros the scale asks for. The longer of the
        // two is the length, so both have to fit.
        return sign + 2 + scale <= MAX_SPELT_OUT_DIGITS
                && hasAtMostDigits(d, MAX_SPELT_OUT_DIGITS - 1 - sign);
    }

    /**
     * Whether {@code d} carries at most {@code limit} significant digits, answered from the bit
     * length of its unscaled value and not by counting them: a count of a large value is work that
     * grows faster than the value does.
     *
     * <p>A number of at most {@code 3 × limit} bits is below {@code 2^(3 × limit)}, which is below
     * {@code 10^limit}, and a number of more than {@code 4 × limit} bits is past
     * {@code 2^(4 × limit)}, which is past {@code 10^limit}. Only a value between the two is
     * compared with {@code 10^limit}, and that is a value of at most {@code 4 × limit} bits, so the
     * power built is no larger than the value compared. A caller's limit is meant to be a bound on a
     * notation, a thousand and not a million.
     */
    public static boolean hasAtMostDigits(BigDecimal d, long limit) {
        if (limit < 1) {
            return false;
        }
        if (everyDecimalHasAtMost(limit)) {
            return true;
        }
        BigInteger unscaled = d.unscaledValue();
        if (bitsSayAtMostDigits(unscaled, limit)) {
            return true;
        }
        if (unscaled.bitLength() > 4 * limit) {
            return false;
        }
        return unscaled.abs().compareTo(BigInteger.TEN.pow(Math.toIntExact(limit))) < 0;
    }

    /**
     * Whether a limit is past what any decimal has in digits. Asked before the bit counts, which
     * are multiples of the limit and stay within a long only for a limit below it.
     */
    private static boolean everyDecimalHasAtMost(long limit) {
        return limit >= MOST_DIGITS_ANY_DECIMAL_HOLDS;
    }

    /**
     * Whether the bit length of {@code unscaled} alone shows it has at most {@code limit} digits,
     * for a limit that {@link #everyDecimalHasAtMost} has not already settled.
     */
    private static boolean bitsSayAtMostDigits(BigInteger unscaled, long limit) {
        long bits = unscaled.bitLength();
        // the least negative number of n bits has a magnitude of n + 1
        long magnitudeBits = unscaled.signum() < 0 ? bits + 1 : bits;
        return magnitudeBits <= 3 * limit;
    }

    /**
     * The most decimal digits a {@code BigInteger} has. Its bit length is an {@code int}, so its
     * magnitude is below {@code 2^Integer.MAX_VALUE}, and that is below {@code 10^646456993}
     * ({@code Integer.MAX_VALUE × log10 2} is 646456992.94…).
     *
     * <p>It is also where the powers of ten that are compared with stop being held: {@code 10^k} is
     * below {@code 2^Integer.MAX_VALUE} for every {@code k} under it, so a {@code BigInteger} holds
     * the power that any limit under it asks for, and a limit at or past it needs none, since every
     * decimal is below it.
     */
    static final long MOST_DIGITS_ANY_DECIMAL_HOLDS = 646_456_993L;

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
        // Fewer zeros than digits, so the scale cannot fall out. Room past what any decimal has in
        // digits settles it without reading the digits; a value the room is not past by its bits
        // takes off the zeros it has, up to the room.
        if (everyDecimalHasAtMost(room) || bitsSayAtMostDigits(d.unscaledValue(), room)) {
            return d.stripTrailingZeros();
        }
        BigInteger digits = d.unscaledValue();
        int zeros = (int) trailingZeros(digits, room);
        return zeros == 0 ? d : new BigDecimal(digits.divide(BigInteger.TEN.pow(zeros)), d.scale() - zeros);
    }

    /**
     * How many zeros {@code digits} ends in, or {@code most} where it ends in more.
     *
     * <p>Found by doubling and then halving, because taking them off one at a time divides the whole
     * number once for each, which is work that grows with the square of its size, and halving the
     * whole range from the start builds a power of ten as large as the range however few zeros there
     * are. Doubling builds none larger than twice the count. Divisible by {@code 10^z} holds for
     * every {@code z} up to the count and for none past it, and a number of n bits has fewer than
     * n / 3 zeros, so that bounds the answer whatever {@code most} says. No number has as many zeros
     * as {@link #MOST_DIGITS_ANY_DECIMAL_HOLDS}, so the powers asked for are ones a {@code BigInteger}
     * holds.
     */
    private static long trailingZeros(BigInteger digits, long most) {
        long upper = Math.min(Math.min(most, digits.bitLength() / 3), MOST_DIGITS_ANY_DECIMAL_HOLDS - 1);
        if (upper < 1 || digits.remainder(BigInteger.TEN).signum() != 0) {
            return 0;
        }
        long lower = 1;
        for (long step = 2; lower < upper; step *= 2) {
            long at = Math.min(step, upper);
            if (digits.remainder(BigInteger.TEN.pow((int) at)).signum() != 0) {
                upper = at - 1;
                break;
            }
            lower = at;
        }
        while (lower < upper) {
            long middle = (lower + upper + 1) / 2;
            if (digits.remainder(BigInteger.TEN.pow((int) middle)).signum() == 0) {
                lower = middle;
            } else {
                upper = middle - 1;
            }
        }
        return lower;
    }

    /**
     * How many chars {@code d.toPlainString()} is, in {@code long} because the answer can be past
     * what an {@code int} counts: a sign, the digits, and either the integer zeros a negative scale
     * stands for or a point with the leading fractional zeros a scale above the precision asks for.
     * Nought is {@code "0"} at every scale up to zero, whatever the scale says.
     *
     * <p>Worked out from the number and its scale, without the text. The text is as long as the
     * scale is far from nought, so a value a few bytes wide can have one no {@code String} holds,
     * and asking how long it is by building it is what fails.
     */
    public static long plainNotationLength(BigDecimal d) {
        long sign = d.signum() < 0 ? 1 : 0;
        long precision = d.precision();
        long scale = d.scale();
        if (scale <= 0) {
            return d.signum() == 0 ? 1 : sign + precision - scale;
        }
        return precision > scale ? sign + precision + 1 : sign + 2 + scale;
    }

    /**
     * The number {@code a} times {@code b}, at whatever scale holds it, or null where no decimal is
     * that number.
     *
     * <p>The scale of the product is the sum of the factors', and {@code BigDecimal.multiply} refuses
     * a nonzero product whose sum leaves the range even where the number is held at another scale:
     * {@code 10 × 10^-2147483647} times {@code 10^-1} is {@code 10^-2147483647}, and a factor at the
     * floor of the range times {@code 10^1} is {@code 10} at the floor. So the digits are multiplied
     * here and moved to the scale the type has: a sum above the range gives up the zeros it is over
     * by, and a sum below it takes the zeros it is short by.
     *
     * <p>Two questions, kept apart as {@code ExactRatio} keeps them. Whether the number has a decimal
     * representation is the language's, and is independent of whether this host has room for its
     * digits: null is a sum above the range that the digits have no zeros to bring back. Whether the
     * host has room is not about the number, so it is never null: a sum below the range asks for
     * zeros no whole number here holds, and that is an {@link ExactFailure}, which a run with more
     * room does not raise.
     *
     * <p>Nought is nought at every scale, so it answers before any scale is summed.
     *
     * @throws ExactFailure where the zeros a sum below the range asks for are more than the host holds
     */
    public static BigDecimal product(BigDecimal a, BigDecimal b) {
        BigInteger digits = a.unscaledValue().multiply(b.unscaledValue());
        if (digits.signum() == 0) {
            return BigDecimal.ZERO;
        }
        long scale = (long) a.scale() + b.scale();
        if (scale > Integer.MAX_VALUE) {
            long excess = scale - Integer.MAX_VALUE;
            if (trailingZeros(digits, excess) < excess) {
                return null;
            }
            digits = digits.divide(BigInteger.TEN.pow((int) excess));
            scale = Integer.MAX_VALUE;
        }
        if (scale < Integer.MIN_VALUE) {
            BigInteger zeros = BigInteger.valueOf(Integer.MIN_VALUE - scale);
            return new BigDecimal(ExactArithmetic.written(digits, zeros, zeros), Integer.MIN_VALUE);
        }
        return new BigDecimal(digits, (int) scale);
    }

    /**
     * The sum of {@code a} and {@code b} at the scale the run time gives it, or null where the
     * representation has no room for it. The run time's {@code +} is this, and aborts on null.
     */
    public static BigDecimal sumWhereThereIsRoom(BigDecimal a, BigDecimal b) {
        try {
            return a.add(b);
        } catch (ArithmeticException _) {
            return null;
        }
    }

    /** The difference of {@code a} and {@code b} as {@link #sumWhereThereIsRoom} gives a sum. */
    public static BigDecimal differenceWhereThereIsRoom(BigDecimal a, BigDecimal b) {
        try {
            return a.subtract(b);
        } catch (ArithmeticException _) {
            return null;
        }
    }

    /**
     * The product of {@code a} and {@code b} at the scale the run time gives it, which is the sum
     * of the factors' scales, or null where the representation has no room for it.
     *
     * <p>That sum is worked out first, and a product whose scale no {@code Decimal} holds has no
     * room whatever its value is. Asked first, {@code BigDecimal} answers some such products
     * instead of refusing them — a nought factor on the left is multiplied at a scale moved back
     * into range, and the same factor on the right is refused — so {@code a * b} and {@code b * a}
     * would differ. A refusal that still comes back is the representation having no room for the
     * product's digits. Distinct from {@link #product}, which is the number and not the run
     * time's representation of it.
     */
    public static BigDecimal timesWhereThereIsRoom(BigDecimal a, BigDecimal b) {
        long scale = (long) a.scale() + b.scale();
        if (scale != (int) scale) {
            return null;
        }
        try {
            return a.multiply(b);
        } catch (ArithmeticException _) {
            return null;
        }
    }
}
