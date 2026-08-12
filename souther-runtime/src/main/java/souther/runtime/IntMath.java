package souther.runtime;

/**
 * Overflow-checked {@code Int} arithmetic (spec §stdlib-int). {@code Int} is signed 64-bit; when a sum,
 * difference, or product leaves that range the computation aborts rather than wrapping. Overflow is a model
 * bug, not a business result, so — like an invariant violation — it throws {@link ConstraintViolation} (spec
 * §algebraic-types, §violation-destination, §jvm-abort), which Souther code cannot catch.
 *
 * <p>Zero division is different: it is a possible input (the divisor is 0), so it returns a
 * {@code DivisionByZero} case rather than aborting (spec §stdlib-int). It is not handled here.
 */
public final class IntMath {

    private IntMath() {}

    public static long addExact(long a, long b) {
        try {
            return Math.addExact(a, b);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Int overflow: " + a + " + " + b);
        }
    }

    public static long subtractExact(long a, long b) {
        try {
            return Math.subtractExact(a, b);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Int overflow: " + a + " - " + b);
        }
    }

    public static long multiplyExact(long a, long b) {
        try {
            return Math.multiplyExact(a, b);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Int overflow: " + a + " * " + b);
        }
    }

    /**
     * The {@code /} operator on Int: truncating division that aborts on a zero divisor (and on the
     * {@code Long.MIN_VALUE / -1} overflow), like the other arithmetic operators (spec §stdlib-int). Code
     * that wants a zero divisor as a case uses the {@code Int.divide} function, which returns
     * {@code Int | DivisionByZero} instead.
     */
    public static long divideExact(long a, long b) {
        if (b == 0) {
            throw new ConstraintViolation("division by zero: " + a + " / 0");
        }
        try {
            return Math.divideExact(a, b);
        } catch (ArithmeticException _) {
            throw new ConstraintViolation("Int overflow: " + a + " / " + b);
        }
    }

    /** {@code Int.compare(a, b)}: -1, 0, or 1. The function form of the comparison operators. */
    public static long compare(long a, long b) {
        return Long.compare(a, b);
    }

    /**
     * {@code Int.floorMod(dividend, divisor)} (spec §stdlib-int): the remainder of a floored division, so
     * the result takes the sign of the divisor — {@code floorMod(-7, 3)} is {@code 2}, where
     * {@code Int.truncatingRemainder(-7, 3)} is {@code -1}.
     *
     * <p>A zero divisor is a model bug — like the {@code /} operator it aborts with
     * {@link ConstraintViolation} rather than returning a case, so the result is a plain {@code Int}
     * that reads in an invariant. That makes this the one standard-library function whose failure is
     * not in its type; {@code Int.truncatingRemainder} is the one to reach for where a zero divisor
     * has to be a business case.
     */
    public static long floorMod(long dividend, long divisor) {
        if (divisor == 0) {
            throw new ConstraintViolation("modulo by zero: floorMod(" + dividend + ", 0)");
        }
        return Math.floorMod(dividend, divisor);
    }
}
