package souther.runtime;

import souther.exact.ExactArithmetic;
import souther.exact.ExactDecimals;
import souther.exact.ExactFailure;
import souther.exact.ExactParts;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

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
        return ExactDecimals.plainNotationLength(d);
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
     * amount and a boundary's canonical number are both taken from. The form is
     * {@link souther.exact.ExactDecimals#leastDigits}, which the compiler reads a number by as well.
     */
    static BigDecimal leastDigits(BigDecimal d) {
        return ExactDecimals.leastDigits(d);
    }

    // What an evaluated class calls: each operation above, paid for to a checkpoint before the host
    // is asked for it (HostWork). Paying is all these add, so what they answer is what the operation
    // answers, refusals included.

    /**
     * The sum of {@code terms}, at the greatest scale any of them is written at and never less than
     * nought's — what adding them up a {@code +} at a time comes to, in whatever order.
     *
     * <p>A run of {@code +} raises each partial sum to the greater scale, so a fine term met by an
     * ordinary one is a number as long as their scales are apart — past what the host builds,
     * where the scales are far enough apart, though the fine term's negation would have cancelled
     * it. So the run is taken only where no partial sum of it can be that long: every partial sum
     * is no larger than every term's size together, written at the greatest scale, and where that
     * is a number the host builds the run is held, and an exact sum held is the sum whatever order
     * made it. Elsewhere the sum is made the way an exact sum of many is
     * ({@link ExactArithmetic#sum}) and written at the scale last.
     *
     * <p>Held to an allowance, what it costs is seen as well, and a run costs what its order makes
     * it — the long way round to a sum the cancelling way reaches cheaply. So held to one it is made
     * by scale from the first ({@link ExactArithmetic#sumByScale}), and what it costs is the
     * terms'.
     */
    public static BigDecimal sum(List<BigDecimal> terms, WorkCheckpoint checkpoint) {
        int scale = 0;
        for (BigDecimal each : terms) {
            scale = Math.max(scale, each.scale());
        }
        if (checkpoint == WorkCheckpoint.NONE && noPartialSumPassesTheHost(terms, scale)) {
            BigDecimal acc = BigDecimal.ZERO;
            for (BigDecimal each : terms) {
                acc = add(acc, each);
            }
            return acc;
        }
        Iterable<ExactParts> parts = () -> terms.stream()
                .map(each -> ExactArithmetic.canonical(each.unscaledValue(), BigInteger.ONE,
                        -(long) each.scale(), -(long) each.scale()))
                .iterator();
        try {
            ExactParts sum = checkpoint == WorkCheckpoint.NONE ? ExactArithmetic.sum(parts)
                    : ExactArithmetic.sumByScale(parts, new Rational.PaidSum(checkpoint));
            // Written at the scale: as long as the sum is, and longer by the powers of ten the
            // scale writes it out to.
            long written = HostWork.bits(sum.numerator()) + HostWork.bitsOfTens(scale);
            HostWork.pay(checkpoint, written, HostWork.power(HostWork.bitsOfTens(scale))
                    + HostWork.product(HostWork.bits(sum.numerator()), written));
            return new BigDecimal(ExactArithmetic.roundedTimesTenTo(sum, scale,
                    java.math.RoundingMode.UNNECESSARY), scale);
        } catch (ExactFailure failure) {
            throw outOfRange("the sum of a list of " + terms.size() + " decimals");
        }
    }

    /**
     * Whether every partial sum a run of {@code +} over {@code terms} makes is a number the host
     * builds: each is no larger than every term's size together, at the greatest {@code scale}.
     */
    private static boolean noPartialSumPassesTheHost(List<BigDecimal> terms, int scale) {
        long bits = 0;
        for (BigDecimal each : terms) {
            long raised = HostWork.bits(each)
                    + HostWork.bitsOfTens((long) scale - each.scale());
            bits = bits > Long.MAX_VALUE - raised ? Long.MAX_VALUE : bits + raised;
            bits = bits == Long.MAX_VALUE ? bits : bits + 1;
        }
        return HostWork.built(bits);
    }

    /**
     * The product of {@code factors}, at the scale their scales add up to — what multiplying them
     * a {@code *} at a time comes to, in whatever order.
     *
     * <p>A product's scale is its factors' scales added up, and is asked to be held once, of the
     * product: a run of {@code *} asks it of every partial product, and two factors past the range
     * together refuse where a third brings the scale back. Paid for to {@code checkpoint} before
     * anything is multiplied, a factor at a time as multiplied into a product as long as every
     * factor together, which no partial product is longer than — so what it costs is the
     * factors'.
     */
    public static BigDecimal product(List<BigDecimal> factors, WorkCheckpoint checkpoint) {
        // Added up wider than a long, so that a scale that passes the end of one and comes back
        // is the scale: as many factors as a list holds can take a long past its end.
        BigInteger allScales = BigInteger.ZERO;
        long all = 0;
        for (BigDecimal each : factors) {
            allScales = allScales.add(BigInteger.valueOf(each.scale()));
            long bits = HostWork.bits(each);
            all = all > Long.MAX_VALUE - bits ? Long.MAX_VALUE : all + bits;
        }
        if (allScales.bitLength() >= Integer.SIZE) {
            throw outOfRange("the product of a list of " + factors.size() + " decimals");
        }
        int scale = allScales.intValueExact();
        if (checkpoint != WorkCheckpoint.NONE) {
            for (BigDecimal each : factors) {
                checkpoint.spend(HostWork.product(HostWork.bits(each), all));
            }
        }
        BigInteger unscaled = BigInteger.ONE;
        for (BigDecimal each : factors) {
            unscaled = unscaled.multiply(each.unscaledValue());
        }
        return new BigDecimal(unscaled, scale);
    }

    /** {@link #add(BigDecimal, BigDecimal)}, paid for to {@code checkpoint} first. */
    public static BigDecimal add(BigDecimal a, BigDecimal b, WorkCheckpoint checkpoint) {
        paySum(a, b, checkpoint);
        return add(a, b);
    }

    /** {@link #subtract(BigDecimal, BigDecimal)}, paid for to {@code checkpoint} first. */
    public static BigDecimal subtract(BigDecimal a, BigDecimal b, WorkCheckpoint checkpoint) {
        paySum(a, b, checkpoint);
        return subtract(a, b);
    }

    /** {@link #multiply(BigDecimal, BigDecimal)}, paid for to {@code checkpoint} first. */
    public static BigDecimal multiply(BigDecimal a, BigDecimal b, WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE) {
            long answer = HostWork.bits(a) + HostWork.bits(b);
            HostWork.pay(checkpoint, answer, HostWork.read(HostWork.bits(a), HostWork.bits(b), answer)
                    + HostWork.product(HostWork.bits(a), HostWork.bits(b)));
        }
        return multiply(a, b);
    }

    /** {@link #divide(BigDecimal, BigDecimal, long, RoundingMode)}, paid for to {@code checkpoint}
     *  first, where it divides at all. */
    public static Object divide(BigDecimal dividend, BigDecimal divisor, long scale, RoundingMode mode,
                                WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE && divisor.signum() != 0 && scale == (int) scale) {
            // The dividend or the divisor is raised by the power of ten that brings the quotient to
            // the scale asked for, and the quotient is as long as what is left after dividing.
            long tens = scale - dividend.scale() + divisor.scale();
            long raise = tens == 0 ? 0 : HostWork.bitsOfTens(tens);
            long over = HostWork.bits(dividend) + (tens > 0 ? raise : 0);
            long under = HostWork.bits(divisor) + (tens < 0 ? raise : 0);
            long quotient = Math.max(over - under, 0) + 1;
            HostWork.pay(checkpoint, Math.max(over, under), HostWork.read(over, under, quotient)
                    + (raise == 0 ? 0 : HostWork.power(raise)
                            + HostWork.product(tens > 0 ? HostWork.bits(dividend) : HostWork.bits(divisor), raise))
                    + HostWork.product(quotient, under));
        }
        return divide(dividend, divisor, scale, mode);
    }

    /** {@link #negate(BigDecimal)}, paid for to {@code checkpoint} first. */
    public static BigDecimal negate(BigDecimal d, WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE) {
            checkpoint.spend(HostWork.read(HostWork.bits(d), HostWork.bits(d)));
        }
        return negate(d);
    }

    /** {@link #compare(BigDecimal, BigDecimal)}, paid for to {@code checkpoint} first. */
    public static long compare(BigDecimal a, BigDecimal b, WorkCheckpoint checkpoint) {
        payComparison(a, b, checkpoint);
        return compare(a, b);
    }

    /** {@link #toInt(RoundingMode, BigDecimal)}, paid for to {@code checkpoint} first. */
    public static long toInt(RoundingMode mode, BigDecimal d, WorkCheckpoint checkpoint) {
        payRescaled(d, 0, checkpoint);
        return toInt(mode, d);
    }

    /** {@link #round(long, RoundingMode, BigDecimal)}, paid for to {@code checkpoint} first, where
     *  the scale is one the run time takes. */
    public static BigDecimal round(long scale, RoundingMode mode, BigDecimal d, WorkCheckpoint checkpoint) {
        if (scale == (int) scale) {
            payRescaled(d, (int) scale, checkpoint);
        }
        return round(scale, mode, d);
    }

    /** {@link #plainText(BigDecimal)}, paid for to {@code checkpoint} first: the digits turned into
     *  text, which multiplies, and the text written. */
    public static String plainText(BigDecimal d, WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE) {
            long digits = HostWork.bits(d);
            checkpoint.spend(HostWork.power(digits) + HostWork.product(digits, digits));
            long length = plainTextLength(d);
            if (length <= Strings.LONGEST_TEXT) {
                checkpoint.spend(HostWork.read(length * Character.SIZE));
            }
        }
        return plainText(d);
    }

    /** {@link #ofDecimalText(String)}, paid for to {@code checkpoint} first: reading digits into a
     *  whole number multiplies what has been read by ten for every few digits more. */
    static BigDecimal ofDecimalText(String text, WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE) {
            long bits = HostWork.bitsOfTens(text.length());
            HostWork.pay(checkpoint, bits, HostWork.product(bits, bits));
        }
        return ofDecimalText(text);
    }

    /** {@link #leastDigits(BigDecimal)}, paid for to {@code checkpoint} first: taking the zeros off
     *  divides the digits by ten as many times as there are zeros to take. */
    static BigDecimal leastDigits(BigDecimal d, WorkCheckpoint checkpoint) {
        if (checkpoint != WorkCheckpoint.NONE) {
            long bits = HostWork.bits(d);
            checkpoint.spend(HostWork.power(bits) + HostWork.product(bits, bits));
        }
        return leastDigits(d);
    }

    // Each estimate below follows what the host decides before it computes, in the order it decides
    // it, and pays only for the work that decision leaves: a nought or a sign settles a comparison,
    // and a nought brought to another scale is a nought. A scale is paid for only where the host
    // builds a number at it, and then because the number is that long.

    /** Pays for a sum or a difference: the operand at the smaller scale is multiplied by the power of
     *  ten between the two scales, unless it is nought, and the answer is as long as the longer of the
     *  two once that is done. */
    private static void paySum(BigDecimal a, BigDecimal b, WorkCheckpoint checkpoint) {
        if (checkpoint == WorkCheckpoint.NONE) {
            return;
        }
        BigDecimal raised = a.scale() < b.scale() ? a : b;
        BigDecimal kept = raised == a ? b : a;
        long gap = Math.abs((long) a.scale() - b.scale());
        long raise = gap == 0 || raised.signum() == 0 ? 0 : HostWork.bitsOfTens(gap);
        long answer = Math.max(HostWork.bits(raised) + raise, HostWork.bits(kept)) + 1;
        HostWork.pay(checkpoint, answer, HostWork.read(HostWork.bits(a), HostWork.bits(b), answer)
                + (raise == 0 ? 0 : HostWork.power(raise) + HostWork.product(HostWork.bits(raised), raise)));
    }

    /**
     * Pays for a comparison. A nought or two signs apart is settled on sight. Otherwise the host
     * counts each operand's digits, which compares it with a power of ten as long, and compares where
     * the first digit of each stands; only two values whose first digits stand at one place are brought
     * to one scale, and then the scales are no further apart than the digits are many — so what that
     * costs is bounded by how long the operands are, whatever their scales.
     */
    private static void payComparison(BigDecimal a, BigDecimal b, WorkCheckpoint checkpoint) {
        if (checkpoint == WorkCheckpoint.NONE) {
            return;
        }
        long bitsA = HostWork.bits(a);
        long bitsB = HostWork.bits(b);
        if (a.signum() == 0 || b.signum() == 0 || a.signum() != b.signum()) {
            checkpoint.spend(HostWork.read(bitsA, bitsB));
            return;
        }
        long counting = HostWork.read(bitsA, bitsB) + HostWork.power(bitsA) + HostWork.power(bitsB);
        // Where the first digit stands, from the bits: a digit is a little over three of them, so the
        // count is off by at most one either way, and two apart is apart.
        long firstA = bitsA * 30103 / 100000 - a.scale();
        long firstB = bitsB * 30103 / 100000 - b.scale();
        if (Math.abs(firstA - firstB) > 2) {
            checkpoint.spend(counting);
            return;
        }
        long longer = Math.max(bitsA, bitsB);
        checkpoint.spend(counting + HostWork.power(longer) + HostWork.product(longer, longer));
    }

    /** Pays for {@code d} brought to {@code places}: multiplied by a power of ten to go up, divided
     *  by one to go down. A nought is a nought at every scale, and costs the reading. */
    private static void payRescaled(BigDecimal d, int places, WorkCheckpoint checkpoint) {
        if (checkpoint == WorkCheckpoint.NONE) {
            return;
        }
        if (d.signum() == 0) {
            checkpoint.spend(HostWork.read(HostWork.bits(d)));
            return;
        }
        long gap = (long) places - d.scale();
        long raise = gap == 0 ? 0 : HostWork.bitsOfTens(gap);
        long answer = HostWork.bits(d) + (gap > 0 ? raise : 0);
        HostWork.pay(checkpoint, Math.max(answer, raise), HostWork.read(HostWork.bits(d), answer)
                + (raise == 0 ? 0 : HostWork.power(raise) + HostWork.product(HostWork.bits(d), raise)));
    }
}
