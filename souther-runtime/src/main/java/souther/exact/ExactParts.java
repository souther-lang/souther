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

    public static final ExactParts ZERO = new ExactParts(BigInteger.ZERO, BigInteger.ONE, 0, 0);

    public boolean isZero() {
        return numerator.signum() == 0;
    }

    public int signum() {
        return numerator.signum();
    }
}
