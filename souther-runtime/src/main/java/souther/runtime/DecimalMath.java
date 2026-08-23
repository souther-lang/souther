package souther.runtime;

import java.math.BigDecimal;
import java.math.MathContext;
import java.util.function.Supplier;

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
 * difference, a product or a quotient whose scale leaves what a {@code BigDecimal} holds raises
 * {@code ArithmeticException} — so each runs through {@link #aborting}, which reports it the way an
 * {@code Int} overflow is reported (spec §jvm-abort). Neither is a business result.
 */
public final class DecimalMath {

    private DecimalMath() {}

    /** The rounding of the {@code /} operator: F#/.NET System.Decimal precision, half away from zero. */
    private static final MathContext DIVIDE = new MathContext(29, java.math.RoundingMode.HALF_UP);

    /**
     * Runs a {@code BigDecimal} operation and reports the way it refuses as the abort it is.
     *
     * <p>{@code BigDecimal} answers on a range and not on every pair: a result whose scale leaves
     * the 32 bits a scale is kept in raises {@code ArithmeticException} — "Overflow", "Underflow",
     * or "BigInteger would overflow supported range" — and that is every operation here, the sum and
     * the product included. Left alone it arrives at a boundary as a {@code java.math} exception
     * from a program that has no such type. It is the same kind of thing an {@code Int} overflow is
     * ({@link IntMath}): a model bug rather than a business result, so it aborts.
     */
    private static <T> T aborting(Supplier<T> operation, String what) {
        try {
            return operation.get();
        } catch (ArithmeticException _) {
            throw new ConstraintViolation(what + " is outside the range a Decimal holds");
        }
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
     * operation asked for at that scale has an answer is {@link #aborting}'s question: a scale of
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
        return aborting(() -> a.add(b), "the sum of " + describe(a) + " and " + describe(b));
    }

    /** {@code Decimal.subtract(a, b)}, and the {@code -} operator. */
    public static BigDecimal subtract(BigDecimal a, BigDecimal b) {
        return aborting(() -> a.subtract(b),
                "the difference of " + describe(a) + " and " + describe(b));
    }

    /** {@code Decimal.multiply(a, b)}, and the {@code *} operator. A product's scale is the sum of
     *  its factors' scales, so this is the operation that reaches the end of the range first. */
    public static BigDecimal multiply(BigDecimal a, BigDecimal b) {
        return aborting(() -> a.multiply(b),
                "the product of " + describe(a) + " and " + describe(b));
    }

    /**
     * The {@code /} operator on Decimal (spec §stdlib-decimal). A zero divisor aborts, like the
     * other arithmetic operators — code that wants it as a case uses the {@code Decimal.divide}
     * function below, which returns {@code Decimal | DivisionByZero}.
     *
     * <p>The quotient is rounded to a significant-digit precision matching F#/.NET
     * {@code System.Decimal} (about 28–29 digits), rounding half away from zero (HALF_UP), so
     * {@code 10m / 3m} is {@code 3.3333…} rather than aborting on a non-terminating result. When a
     * specific scale and mode are part of the domain, {@code Decimal.divide(a, b, scale, mode)}
     * states them explicitly.
     */
    public static BigDecimal divide(BigDecimal a, BigDecimal b) {
        if (b.signum() == 0) {
            throw new ConstraintViolation("division by zero: " + describe(a) + " / 0");
        }
        return aborting(() -> a.divide(b, DIVIDE), "the quotient of " + describe(a) + " and " + describe(b));
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
        return aborting(() -> dividend.divide(divisor, places, toJava(mode)),
                "the quotient of " + describe(dividend) + " and " + describe(divisor)
                        + " at scale " + scale);
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
        BigDecimal whole = aborting(() -> d.setScale(0, toJava(mode)),
                "the whole number " + describe(d) + " rounds to");
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
        return aborting(() -> d.setScale(places, toJava(mode)),
                describe(d) + " rounded to scale " + scale);
    }
}
