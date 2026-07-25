package souther.runtime;

import java.math.BigDecimal;
import java.math.MathContext;
import java.math.RoundingMode;

/**
 * The {@code /} operator on Decimal (spec 18.1). A zero divisor aborts, like the other arithmetic
 * operators — code that wants it as a case uses the {@code Decimal.divide} function, which returns
 * {@code Decimal | DivisionByZero}.
 *
 * <p>The quotient is rounded to a significant-digit precision matching F#/.NET {@code System.Decimal}
 * (about 28–29 digits), rounding half away from zero (HALF_UP), so {@code 10m / 3m} is
 * {@code 3.3333…} rather than aborting on a non-terminating result. When a specific scale and mode
 * are part of the domain, {@code Decimal.divide(a, b, scale, mode)} states them explicitly.
 */
public final class DecimalMath {

    private DecimalMath() {}

    /** The rounding of the {@code /} operator: F#/.NET System.Decimal precision, half away from zero. */
    private static final MathContext DIVIDE = new MathContext(29, RoundingMode.HALF_UP);

    public static BigDecimal divide(BigDecimal a, BigDecimal b) {
        if (b.signum() == 0) {
            throw new ConstraintViolation("division by zero: " + a.toPlainString() + " / 0");
        }
        return a.divide(b, DIVIDE);
    }

    /** {@code Decimal.compare(a, b)}: -1, 0, or 1 by numeric value, ignoring scale. */
    public static long compare(BigDecimal a, BigDecimal b) {
        return a.compareTo(b);
    }

    /** {@code Decimal.fromInt(n)}: every Int is a Decimal exactly, so the widening needs nothing
     *  stated. The narrowing does — see {@link #toInt}. */
    public static BigDecimal fromInt(long n) {
        return BigDecimal.valueOf(n);
    }

    /**
     * {@code Decimal.toInt(d, mode)}: the whole number {@code d} rounds to under {@code mode}. The
     * mode is written at the call because dropping a fraction is a domain decision — a tax is
     * truncated or rounded by rule, not by default — the same reason {@code Decimal.divide} states
     * its scale and mode.
     *
     * <p>A value too large for {@code Int} aborts, as an Int overflow does ({@link IntMath}): it is a
     * model bug rather than a business result.
     */
    public static long toInt(BigDecimal d, RoundingMode mode) {
        try {
            return d.setScale(0, mode).longValueExact();
        } catch (ArithmeticException e) {
            throw new ConstraintViolation("Decimal does not fit in an Int: " + d.toPlainString());
        }
    }
}
