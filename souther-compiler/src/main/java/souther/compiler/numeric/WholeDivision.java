package souther.compiler.numeric;

import java.math.BigInteger;

/**
 * A whole number divided by another and rounded to a whole number one way or the other.
 *
 * <p>{@link BigInteger#divide} rounds towards nought, which is the floor above nought and the
 * ceiling below it: {@code -7 / 3} is {@code -2}, whose floor is {@code -3}. A reader working out
 * the least or the greatest whole number on one side of a bound wants one of the two whichever way
 * the numbers' signs fall, so the two are answered here for every sign of either number.
 */
public final class WholeDivision {

    private WholeDivision() {
    }

    /**
     * The greatest whole number no greater than {@code number / by}.
     *
     * @throws ArithmeticException where {@code by} is nought
     */
    public static BigInteger floorOf(BigInteger number, BigInteger by) {
        BigInteger[] both = number.divideAndRemainder(by);
        return both[1].signum() != 0 && both[1].signum() != by.signum()
                ? both[0].subtract(BigInteger.ONE) : both[0];
    }

    /**
     * The least whole number no less than {@code number / by}.
     *
     * @throws ArithmeticException where {@code by} is nought
     */
    public static BigInteger ceilingOf(BigInteger number, BigInteger by) {
        return floorOf(number.negate(), by).negate();
    }
}
