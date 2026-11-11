package souther.runtime;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Objects;
import java.util.function.Supplier;

/**
 * Where a number a {@code Rational} or a {@code Decimal} holds is narrowed to an {@code Int}: the one
 * place the bound of an {@code Int} is asked of such a number.
 *
 * <p>The bound is the language's (spec §an-operation-refuses-only-what-its-own-answer-has-no-place-for),
 * so a value past it is refused as a {@link ConstraintViolation} whether or not this run has room
 * to write the whole number it comes to. It is asked of the value by its order, before any whole
 * number is built: building one first would let the run's shortage at the far end of the exponents
 * answer in place of the language's refusal.
 *
 * <p>Rounding moves a value by less than one. So a value at or past one beyond either end of the
 * {@code Int}s rounds past that end under every mode and is refused on its order alone, and a value
 * inside those two rounds to a whole number of at most 64 bits, which is built and then asked
 * exactly, since a value within one of an end can still round past it.
 */
final class IntNarrowing {

    private static final Rational LEAST = Rational.of(Long.MIN_VALUE);
    private static final Rational GREATEST = Rational.of(Long.MAX_VALUE);
    private static final Rational ONE_BELOW_EVERY_INT = Rational.of(
            BigInteger.valueOf(Long.MIN_VALUE).subtract(BigInteger.ONE), BigInteger.ONE);
    private static final Rational ONE_ABOVE_EVERY_INT = Rational.of(
            BigInteger.valueOf(Long.MAX_VALUE).add(BigInteger.ONE), BigInteger.ONE);

    /**
     * Whole digits a decimal may have and round into an {@code Int} under every mode: below ten to
     * the eighteen, which rounds to at most ten to the eighteen, inside the {@code Int}s.
     */
    private static final long WHOLE_DIGITS_EVERY_MODE_KEEPS = 18;

    private IntNarrowing() {
    }

    /** The {@code Int} {@code r} rounds to by {@code mode}, or a refusal where it is no
     *  {@code Int}; {@code what} names the number in the refusal. */
    static long rounded(Rational r, java.math.RoundingMode mode, WorkCheckpoint checkpoint,
                        Supplier<String> what) {
        if (r.compareTo(ONE_BELOW_EVERY_INT, checkpoint) <= 0
                || r.compareTo(ONE_ABOVE_EVERY_INT, checkpoint) >= 0) {
            throw noInt(what);
        }
        BigDecimal whole = r.asDecimal(0, mode, checkpoint);
        if (whole.compareTo(BigDecimal.valueOf(Long.MIN_VALUE)) < 0
                || whole.compareTo(BigDecimal.valueOf(Long.MAX_VALUE)) > 0) {
            throw noInt(what);
        }
        return whole.longValue();
    }

    /**
     * The {@code Int} {@code d} rounds to by {@code mode}, as {@link #rounded(Rational,
     * java.math.RoundingMode, WorkCheckpoint, Supplier)} answers of the same number.
     *
     * <p>A decimal with no more whole digits than every mode keeps inside the {@code Int}s is
     * rounded as it is written, which is the same number and the common case; any other is asked
     * as the exact number it is.
     */
    static long rounded(BigDecimal d, java.math.RoundingMode mode, WorkCheckpoint checkpoint,
                        Supplier<String> what) {
        if ((long) d.precision() - d.scale() <= WHOLE_DIGITS_EVERY_MODE_KEEPS) {
            DecimalMath.payRescaled(d, 0, checkpoint);
            try {
                return d.setScale(0, mode).longValueExact();
            } catch (ArithmeticException _) {
                // A scale far enough from nought that rescaling asks for a power of ten the
                // representation has no room for: the answer is near nought all the same.
            }
        }
        return rounded(Rational.of(d, checkpoint), mode, checkpoint, what);
    }

    /** The {@code Int} {@code r} is, which is whole, or a refusal where it is no {@code Int}. */
    static long exactly(Rational r, WorkCheckpoint checkpoint, Supplier<String> what) {
        if (r.compareTo(LEAST, checkpoint) < 0 || r.compareTo(GREATEST, checkpoint) > 0) {
            throw noInt(what);
        }
        return Objects.requireNonNull(r.asWholeNumber(checkpoint)).longValueExact();
    }

    private static ConstraintViolation noInt(Supplier<String> what) {
        return new ConstraintViolation(what.get() + " does not fit in an Int");
    }
}
