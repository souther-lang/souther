package souther.runtime;

import java.math.BigDecimal;

/**
 * The {@code Rational} operators, as the runtime that owns them (ADR-0112).
 *
 * <p>Exact arithmetic has no overflow to check: the value is whatever the operands make, and what is
 * bounded is the exponent a representation holds, which {@link Rational} aborts on for itself. So what
 * is here is the one thing an operator decides that the value does not — a zero divisor, which aborts
 * the way the other zero divisors of the language do (spec §stdlib-int, §jvm-abort) — and the two
 * embeddings a heterogeneous operator performs.
 *
 * <p>The embeddings are the operator's semantics and not a conversion the language offers: an
 * {@code Int} beside a {@code Rational} is read at its exact mathematical value because that is what
 * {@code Rational + Int} means, while an {@code Int} in a Rational position is refused where it is
 * written (ADR-0116). Emitted at the operator, so the value the arithmetic sees is a Rational on both
 * sides and every reader below it — a container, a hash, an order — sees one kind of value.
 */
public final class RationalMath {

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
}
