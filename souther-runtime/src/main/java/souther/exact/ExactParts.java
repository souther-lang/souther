package souther.exact;

import java.math.BigInteger;

/**
 * The four numbers an exact rational is made of:
 *
 * <pre>{@code
 * numerator × 2^twos × 5^fives / denominator
 * }</pre>
 *
 * <p>What a caller hands the arithmetic and what it gets back. Operands are in the canonical form
 * {@link ExactArithmetic#canonical} makes; an answer is a value of the right size that is not
 * necessarily in that form, and the caller's own constructor makes it canonical, so that what is
 * stored is canonical whoever stores it.
 *
 * <p>Not a value type of the language. The two types that are, the compiler's {@code ExactRatio} and
 * the run time's {@code Rational}, are different things with the same arithmetic, and this is what
 * they lend each other for it.
 */
public record ExactParts(BigInteger numerator, BigInteger denominator, long twos, long fives) {

    /**
     * Parts with a nought below the line are no value, canonical or not, so none are made. What
     * the arithmetic forms below the line is a product of denominators it was handed and of a
     * divisor's numerator once nought is turned away, so it never forms one.
     *
     * @throws IllegalArgumentException where the denominator is nought
     */
    public ExactParts {
        if (denominator.signum() == 0) {
            throw new IllegalArgumentException("parts of a value have no nought below the line");
        }
    }

    public static final ExactParts ZERO = new ExactParts(BigInteger.ZERO, BigInteger.ONE, 0, 0);

    /**
     * Written out and not left to the record: {@link ExactArithmetic#compare} asks it first of
     * every pair, and the generated one goes through a method handle on every call. The exponents
     * are compared before the integers, since two values that differ mostly differ there.
     */
    @Override
    public boolean equals(Object other) {
        return this == other || (other instanceof ExactParts parts
                && twos == parts.twos && fives == parts.fives
                && numerator.equals(parts.numerator) && denominator.equals(parts.denominator));
    }

    @Override
    public int hashCode() {
        int hash = numerator.hashCode();
        hash = 31 * hash + denominator.hashCode();
        hash = 31 * hash + Long.hashCode(twos);
        return 31 * hash + Long.hashCode(fives);
    }

    public boolean isZero() {
        return numerator.signum() == 0;
    }

    public int signum() {
        return numerator.signum();
    }
}
