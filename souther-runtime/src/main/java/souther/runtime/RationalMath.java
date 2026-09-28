package souther.runtime;

import java.math.BigDecimal;
import java.util.Objects;

/**
 * The {@code Rational} operators, as the runtime that owns them (ADR-0112).
 *
 * <p>Exact arithmetic has no overflow to check: the value is whatever the operands make. What is bounded
 * is what a representation holds — the width of an exponent, and a decimal's scale — and {@link Rational}
 * aborts on both for itself, at the point a value the bound excludes is asked for rather than at a step on
 * the way to one. What a numerator or a denominator may be is not among them: the operands these operators
 * read into a Rational include every {@code Decimal}, whose unscaled value is a whole number of whatever
 * size the platform holds, so a bound there would refuse a comparison over values the language says are
 * comparable. So what is here
 * is the one thing an operator decides that the value does not — a zero divisor, which aborts the way the
 * other zero divisors of the language do (spec §stdlib-int, §jvm-abort) — and the two embeddings a
 * heterogeneous operator performs.
 *
 * <p>The embeddings are the operator's semantics and not a conversion the language offers: an
 * {@code Int} beside a {@code Rational} is read at its exact mathematical value because that is what
 * {@code Rational + Int} means, while an {@code Int} in a Rational position is refused where it is
 * written (ADR-0116). Emitted at the operator, so the value the arithmetic sees is a Rational on both
 * sides and every reader below it — a container, a hash, an order — sees one kind of value.
 */
public final class RationalMath {

    /** The ends of what an {@code Int} holds, as the values the exact narrowing compares against. */
    private static final Rational LEAST_INT = Rational.of(Long.MIN_VALUE);
    private static final Rational GREATEST_INT = Rational.of(Long.MAX_VALUE);

    private RationalMath() {}

    public static Rational add(Rational a, Rational b) {
        return a.plus(b);
    }

    public static Rational subtract(Rational a, Rational b) {
        return a.minus(b);
    }

    public static Rational multiply(Rational a, Rational b) {
        return a.times(b);
    }

    /**
     * The {@code /} operator: the exact quotient, aborting on a zero divisor as the operator form does
     * for the other numbers. Code that wants a zero divisor as a business case asks for it by the
     * operation that answers one.
     */
    public static Rational divide(Rational a, Rational b) {
        if (b.isZero()) {
            throw new ConstraintViolation("division by zero: " + a + " / 0");
        }
        return a.dividedBy(b);
    }

    public static Rational negate(Rational a) {
        return a.negated();
    }

    /** {@code Int / Int}: the exact quotient of two whole numbers, which is where a model reaches
     *  exact arithmetic without naming it. */
    public static Rational divideWholeNumbers(long dividend, long divisor) {
        if (divisor == 0) {
            throw new ConstraintViolation("division by zero: " + dividend + " / 0");
        }
        return Rational.of(dividend).dividedBy(Rational.of(divisor));
    }

    /** An {@code Int} at its exact value, for the operator that has a Rational on the other side. */
    public static Rational fromInt(long whole) {
        return Rational.of(whole);
    }

    /** A {@code Decimal} at its exact value, for the operator that has a Rational on the other side.
     *  The scale reaches an exponent and no power of ten is built from it. */
    public static Rational fromDecimal(BigDecimal written) {
        return Rational.of(written);
    }

    /** {@code Rational.compare(a, b)}: -1, 0, or 1. The function form of the comparison operators. */
    public static long compare(Rational a, Rational b) {
        return Integer.signum(a.compareTo(b));
    }

    /**
     * {@code Rational.toWholeNumber(r)}: the {@code Int} this exactly is, or {@link NotWhole} — the
     * {@code Int | NotWhole} union.
     *
     * <p>Exact, so it states no rounding and answers a case where the carrier holds no such value.
     * A value too large for an {@code Int} aborts rather than answering that case: the two are
     * different sentences, one saying the number has a fraction and the other that an {@code Int}
     * cannot hold it, and only the first is a business outcome.
     *
     * <p>Which of the two it is, is asked before the digits are. A whole number whose exponents run
     * past what an {@code Int} holds has hundreds of millions of digits, and building them to find that
     * out says the same thing the comparison says for nothing — the comparison reading bounds on the
     * logs and the digits never being what this answers with.
     */
    public static Object toWholeNumber(Rational r) {
        if (!r.isWhole()) {
            return NotWhole.INSTANCE;
        }
        if (r.compareTo(LEAST_INT) < 0 || r.compareTo(GREATEST_INT) > 0) {
            throw new ConstraintViolation("Rational does not fit in an Int: " + r);
        }
        return Objects.requireNonNull(r.asWholeNumber()).longValueExact();
    }

    /** {@code Rational.toFiniteDecimal(r)}: the {@code Decimal} this exactly is, or
     *  {@link NotAFiniteDecimal} — the {@code Decimal | NotAFiniteDecimal} union. Exact for the same
     *  reason, and a third is the case rather than a number of digits somebody chose. */
    public static Object toFiniteDecimal(Rational r) {
        BigDecimal written = r.asDecimal();
        return written == null ? NotAFiniteDecimal.INSTANCE : written;
    }

    /**
     * {@code Rational.toInt(mode, r)}: the whole number this rounds to by {@code mode}. The lossy
     * narrowing, which answers a value because the caller said what to do with the fraction.
     */
    public static long toInt(RoundingMode mode, Rational r) {
        BigDecimal whole = decimalAt(r, 0, mode);
        try {
            return whole.longValueExact();
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Rational does not fit in an Int: " + r);
        }
    }

    /** {@code Rational.toDecimal(scale, mode, r)}: this at {@code scale} places, rounded by
     *  {@code mode}. */
    public static BigDecimal toDecimal(long scale, RoundingMode mode, Rational r) {
        return decimalAt(r, scale, mode);
    }

    /**
     * This as a decimal at {@code scale} places by {@code mode}, so that the two lossy narrowings round
     * the same way and read a scale the same way.
     *
     * <p>Nothing is caught here. What the arithmetic cannot hold is {@link Rational}'s to report, and it
     * reports it as an abort of the language rather than of its host — so an operator that caught the
     * host's exception would be a second place deciding the same thing, and the one place it does not
     * cover is the fold that asks the type directly.
     */
    private static BigDecimal decimalAt(Rational r, long scale, RoundingMode mode) {
        return r.asDecimal(scale(scale), DecimalMath.toJava(mode));
    }

    /** A scale held to what the run time takes, as {@code DecimalMath} holds one. */
    private static int scale(long scale) {
        try {
            return Math.toIntExact(scale);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation(
                    "Rational.toDecimal scale is outside the range the run time takes: " + scale);
        }
    }
}
