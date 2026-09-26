package souther.runtime;

import java.math.BigDecimal;
import java.math.BigInteger;

/**
 * Every Decimal operation the language has (spec §stdlib-decimal), and the one place
 * {@code java.math.BigDecimal} is asked to perform one.
 *
 * <p>The backend knows {@code BigDecimal} as the JVM representation of a {@code Decimal} — it builds
 * a literal, it names the type in a descriptor, it casts to it. What it does not do is implement a
 * Souther operation with a {@code BigDecimal} method: {@code +} emits a call to {@link #add} here,
 * not {@code BigDecimal.add}. Representation is the backend's; what an operation means is this
 * class's (ADR-0112).
 *
 * <p>That line is what closes the two ways {@code java.math} used to reach a Souther boundary as
 * itself. A scale is a Souther {@code Int}, which is 64 bits, and a {@code BigDecimal} takes an
 * {@code int}: the narrowing is {@link #scale}, and it is exact or it aborts, so no division runs at
 * a scale other than the one written. And every one of these operations is partial — a sum, a
 * difference, a product or a quotient can have no value a {@code Decimal} holds — and each reports
 * that as {@link #outOfRange}, the way an {@code Int} overflow is reported (spec §jvm-abort).
 * Neither is a business result.
 *
 * <p>Whether {@code BigDecimal} refuses an operation is not the same question as whether the
 * language has an answer for it. So where the language's rule decides the result's scale from the
 * operands, as it does for a product, the scale is worked out here and checked against the range
 * before {@code BigDecimal} is asked; what {@code BigDecimal} still refuses is caught and reported
 * the same way.
 */
public final class DecimalMath {

    private DecimalMath() {}

    /**
     * The abort an operation with no value a {@code Decimal} holds is reported as.
     *
     * <p>An operation here answers on a range and not on every pair: a result whose scale leaves
     * the 32 bits a scale is kept in, or whose digits the representation has no room for, is not a
     * {@code Decimal}. {@code BigDecimal} refuses most of those with {@code ArithmeticException} —
     * "Overflow", "Underflow", or "BigInteger would overflow supported range" — which left alone
     * arrives at a boundary as a {@code java.math} exception from a program that has no such type.
     * It is the same kind of thing an {@code Int} overflow is ({@link IntMath}): a model bug rather
     * than a business result, so it aborts.
     *
     * <p>Each operation catches the exception itself and builds {@code what} in the {@code catch}.
     * The message names both operands through {@link #describe}, which walks their digits, and an
     * operation that answers — which is every one in a loop that runs — must not pay for the
     * message of the one that does not. So the operation is written where it stands, as a call and
     * a return, and only this is shared.
     */
    private static ConstraintViolation outOfRange(String what) {
        return new ConstraintViolation(what + " is outside the range a Decimal holds");
    }

    /**
     * What a {@code Decimal} is, in a few numbers, for a message.
     *
     * <p>Not the digits. A message is written where an operation has already run out of range, and
     * the value it ran out on is one whose plain notation is as long as its scale — a value at the
     * far end of the scale range spells out to two billion characters, so writing the digits would
     * ask for the allocation the operation just refused to make. What went wrong is said in numbers
     * that are bounded whatever the value is.
     */
    private static String describe(BigDecimal d) {
        return "sign " + d.signum() + ", precision " + d.precision() + ", scale " + d.scale();
    }

    /**
     * The scale as the run time takes it: the same number, or an abort.
     *
     * <p>A scale is a Souther {@code Int}, which is 64 bits (spec §primitives), and what a
     * {@code BigDecimal} is given is an {@code int}. A raw narrowing drops the high bits, so a scale
     * of {@code 4294967298} would divide at scale 2 — a division at a scale that is neither what was
     * written nor an error, which is the shape §stdlib-int refuses everywhere else. So it is exact
     * or it is nothing.
     *
     * <p>This answers whether the number can be handed over unchanged, and nothing else. Whether the
     * operation asked for at that scale has an answer is {@link #outOfRange}'s question: a scale of
     * {@code 2147483647} passes here — an {@code int} holds it exactly — and a division at it still
     * has no result a {@code BigDecimal} can hold. The two are separate because they fail for
     * separate reasons, and a message calling the second one a scale out of range would be wrong
     * about a scale that was handed over exactly.
     */
    private static int scale(long scale, String what) {
        try {
            return Math.toIntExact(scale);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation(
                    what + " scale is outside the range the run time takes: " + scale);
        }
    }

    /**
     * The Java constant a {@link RoundingMode} value denotes. The mapping sits on the Decimal
     * runtime rather than on the value: {@code java.math} is this backend's implementation detail,
     * not part of what a rounding mode is.
     */
    public static java.math.RoundingMode toJava(RoundingMode mode) {
        return switch (mode) {
            case HALF_UP _ -> java.math.RoundingMode.HALF_UP;
            case HALF_EVEN _ -> java.math.RoundingMode.HALF_EVEN;
            case HALF_DOWN _ -> java.math.RoundingMode.HALF_DOWN;
            case UP _ -> java.math.RoundingMode.UP;
            case DOWN _ -> java.math.RoundingMode.DOWN;
            case CEILING _ -> java.math.RoundingMode.CEILING;
            case FLOOR _ -> java.math.RoundingMode.FLOOR;
        };
    }

    /** {@code Decimal.add(a, b)}, and the {@code +} operator. */
    public static BigDecimal add(BigDecimal a, BigDecimal b) {
        try {
            return a.add(b);
        } catch (ArithmeticException _) {
            throw outOfRange("the sum of " + describe(a) + " and " + describe(b));
        }
    }

    /** {@code Decimal.subtract(a, b)}, and the {@code -} operator. */
    public static BigDecimal subtract(BigDecimal a, BigDecimal b) {
        try {
            return a.subtract(b);
        } catch (ArithmeticException _) {
            throw outOfRange("the difference of " + describe(a) + " and " + describe(b));
        }
    }

    /**
     * {@code Decimal.multiply(a, b)}, and the {@code *} operator. A product's scale is the sum of
     * its factors' scales, so this is the operation that reaches the end of the range first.
     *
     * <p>That sum is worked out here, and a product whose scale no {@code Decimal} holds aborts
     * before {@code BigDecimal} is asked for it, whatever the product's value is. Asked first,
     * {@code BigDecimal} answers some such products instead of refusing them — a nought factor on the
     * left is multiplied at a scale moved back into range, and the same factor on the right is
     * refused — so {@code a * b} and {@code b * a} would differ. A refusal that still comes back is
     * the representation having no room for the product's digits.
     */
    public static BigDecimal multiply(BigDecimal a, BigDecimal b) {
        long scale = (long) a.scale() + b.scale();
        if (scale != (int) scale) {
            throw outOfRange("the product of " + describe(a) + " and " + describe(b));
        }
        try {
            return a.multiply(b);
        } catch (ArithmeticException _) {
            throw outOfRange("the product of " + describe(a) + " and " + describe(b));
        }
    }

    /**
     * {@code Decimal.divide(dividend, divisor, scale, mode)}: the quotient rounded to {@code scale}
     * places by {@code mode}, or {@link DivisionByZero} (spec §stdlib-decimal). A zero divisor is a
     * possible input rather than a model bug, so it is a case; everything else here aborts.
     *
     * <p>The zero divisor is answered before the scale is looked at. A division that does not run
     * needs no scale to run at, so a call with both a zero divisor and a scale no {@code int} holds
     * answers {@code DivisionByZero} — the case the model can handle, not an abort about a number
     * nothing was going to be divided at. Which of the two is asked first is what the answer is, so
     * it is stated in the spec rather than left here (spec §stdlib-decimal).
     *
     * <p>That the arguments are all evaluated before this is entered is the ordinary rule for a
     * call: only {@code &&} and {@code ||} decide which of their operands run (spec
     * §a-condition-stops-when-its-answer-is-settled). The backend used to emit this operation itself
     * and skipped evaluating the scale and the mode on the zero-divisor branch, which was a
     * short-circuit no declaration wrote down.
     */
    public static Object divide(BigDecimal dividend, BigDecimal divisor, long scale, RoundingMode mode) {
        if (divisor.signum() == 0) {
            return DivisionByZero.INSTANCE;
        }
        int places = scale(scale, "Decimal.divide");
        try {
            return dividend.divide(divisor, places, toJava(mode));
        } catch (ArithmeticException _) {
            throw outOfRange("the quotient of " + describe(dividend) + " and " + describe(divisor)
                    + " at scale " + scale);
        }
    }

    /**
     * The unary {@code -} on Decimal. Total — the scale is the operand's and only the sign moves, so
     * there is no scale for a result to leave the range at.
     *
     * <p>Here anyway. The backend may call a host method that answers on every value it is handed
     * (ADR-0112), and this is one, so nothing would be unsound about emitting
     * {@code BigDecimal.negate} where it stands. What decides it is that whoever writes the next
     * Decimal operation would have to answer the same question again, and {@code BigDecimal} does
     * not answer it in its signatures: every one of these throws an unchecked
     * {@code ArithmeticException} or none of them does, and which is which is found by reading the
     * JDK. It was already answered wrong for the sum, the difference and the product, in a comment
     * that said Decimal does not overflow. So the backend keeps none of them and the question is
     * not asked again.
     */
    public static BigDecimal negate(BigDecimal d) {
        return d.negate();
    }

    /** {@code Decimal.compare(a, b)}: -1, 0, or 1 by numeric value, ignoring scale. Total: comparing
     *  builds no value, so there is no scale for a result to leave the range at. */
    public static long compare(BigDecimal a, BigDecimal b) {
        return a.compareTo(b);
    }

    /** {@code Decimal.fromInt(n)}: every Int is a Decimal exactly, so the widening needs nothing
     *  stated. The narrowing does — see {@link #toInt}. */
    public static BigDecimal fromInt(long n) {
        return BigDecimal.valueOf(n);
    }

    /**
     * {@code Decimal.toInt(mode, d)}: the whole number {@code d} rounds to under {@code mode}. The
     * mode is an argument because dropping a fraction is a domain decision — a tax is truncated or
     * rounded by rule, not by default — the same reason {@code Decimal.divide} states its scale and
     * mode.
     *
     * <p>A value too large for {@code Int} aborts, as an Int overflow does ({@link IntMath}): it is a
     * model bug rather than a business result. So does a value the rounding to a whole number cannot
     * be taken of at all, which is a different failure of the same operation and says so.
     */
    public static long toInt(RoundingMode mode, BigDecimal d) {
        BigDecimal whole;
        try {
            whole = d.setScale(0, toJava(mode));
        } catch (ArithmeticException _) {
            throw outOfRange("the whole number " + describe(d) + " rounds to");
        }
        try {
            return whole.longValueExact();
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Decimal does not fit in an Int: " + describe(d));
        }
    }

    /** {@code Decimal.round(scale, mode, d)}: {@code d} rounded to {@code scale} places by
     *  {@code mode}. The parameters are in the order the core declaration writes them — the kernel's
     *  descriptor is derived from that declaration, so the two cannot drift apart. */
    public static BigDecimal round(long scale, RoundingMode mode, BigDecimal d) {
        int places = scale(scale, "Decimal.round");
        try {
            return d.setScale(places, toJava(mode));
        } catch (ArithmeticException _) {
            throw outOfRange(describe(d) + " rounded to scale " + scale);
        }
    }

    /**
     * {@code String.fromDecimal(d)}: {@code d} in plain notation (spec §stdlib-string).
     *
     * <p>Plain notation is as long as the scale is far from nought, whichever way — a scale of
     * {@code -2000000000} is two billion integer zeros, and one of {@code 2000000000} is two billion
     * fractional digits — so a {@code Decimal} a few bytes wide can have a text no {@code String}
     * holds ({@link Strings#LONGEST_TEXT}). That text is an answer with no place, the same abort a
     * {@code String.repeat} count no {@code String} could hold is. The length is worked out before
     * the text is, because {@code toPlainString} answers such a value with
     * {@code ArithmeticException} at the floor of the scale range and with {@code OutOfMemoryError}
     * everywhere else past it.
     */
    public static String plainText(BigDecimal d) {
        if (plainTextLength(d) > Strings.LONGEST_TEXT) {
            throw new ConstraintViolation(
                    "the plain notation of " + describe(d) + " is longer than a String holds");
        }
        return d.toPlainString();
    }

    /**
     * How many chars {@code d.toPlainString()} is, in {@code long} because the answer can be past
     * what an {@code int} counts: a sign, the digits, and either the integer zeros a negative scale
     * stands for or a point with the leading fractional zeros a scale above the precision asks for.
     * Nought is {@code "0"} at every scale up to zero, whatever the scale says.
     */
    static long plainTextLength(BigDecimal d) {
        long sign = d.signum() < 0 ? 1 : 0;
        long precision = d.precision();
        long scale = d.scale();
        if (scale <= 0) {
            return d.signum() == 0 ? 1 : sign + precision - scale;
        }
        return precision > scale ? sign + precision + 1 : sign + 2 + scale;
    }

    /**
     * {@code text} as a {@code Decimal}, at the scale its fractional digits give it. {@code text} is
     * decimal text (spec §string-decimal-text), which {@link Strings#toDecimal} has already decided;
     * {@code BigDecimal(String)} on such text answers without an exponent to overflow and with a
     * scale no longer than a {@code String} is, so it never refuses it.
     */
    static BigDecimal ofDecimalText(String text) {
        return new BigDecimal(text);
    }

    /**
     * The amount {@code d} is, carried by as few digits as a {@code BigDecimal} can carry it: one
     * form for every value the language calls equal (spec §primitives), which is what a hash of an
     * amount and a boundary's canonical number are both taken from.
     *
     * <p>{@code stripTrailingZeros} is that, until the scale it would need is one the type cannot
     * say: a scale is an {@code int}, and taking the zero off {@code (10, MIN_VALUE)} asks for
     * {@code MIN_VALUE - 1}, which it answers by throwing. Stopping at the floor instead still leaves
     * one form per amount — {@code (10, MIN_VALUE)} and {@code (100, MIN_VALUE + 1)} are one amount
     * and both stop at {@code (10, MIN_VALUE)} — because fixing the scale fixes the digits.
     */
    static BigDecimal leastDigits(BigDecimal d) {
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
}
