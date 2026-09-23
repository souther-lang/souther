package souther.exact;

import java.math.BigInteger;

/**
 * Exponents as sixty-four-bit numbers, and the powers built from them.
 *
 * <p>Two questions are asked here and kept apart. Whether an exponent is one this arithmetic holds is
 * about the value, and its failure is {@link ExactRangeExceeded}. Whether a whole number of some size is
 * one the host addresses is about the host, and it is asked before the number is built: a power the host
 * has no room for is not refused on sight but computed until it does not fit, which is minutes and
 * hundreds of megabytes for an answer that was never going to come.
 */
final class ExactPowers {

    static final BigInteger FIVE = BigInteger.valueOf(5);

    private ExactPowers() {
    }

    /** Two exponents added, or the failure of a sum past sixty-four bits. */
    static long added(long exponent, long by) {
        try {
            return Math.addExact(exponent, by);
        } catch (ArithmeticException _) {
            throw new ExactRangeExceeded("exponent out of range: " + exponent + " + " + by);
        }
    }

    /** Two exponents subtracted. The difference of two held exponents is a quotient's as much as their
     *  sum is a product's, so it is held to the same width. */
    static long lessened(long exponent, long by) {
        try {
            return Math.subtractExact(exponent, by);
        } catch (ArithmeticException _) {
            throw new ExactRangeExceeded("exponent out of range: " + exponent + " - " + by);
        }
    }

    /** An exponent negated, which the least sixty-four-bit number is not. */
    static long negated(long exponent) {
        try {
            return Math.negateExact(exponent);
        } catch (ArithmeticException _) {
            throw new ExactRangeExceeded("exponent out of range: -(" + exponent + ")");
        }
    }

    /** An exponent as a power something is about to be built to. */
    static int buildable(long exponent) {
        if (exponent < 0 || exponent > Integer.MAX_VALUE) {
            throw new ExactRangeExceeded("nothing is built at a power of " + exponent);
        }
        return (int) exponent;
    }

    /** The same of an exponent held wider than a long, which the sum of an exponent and a scale is. */
    static int buildable(BigInteger exponent) {
        if (exponent.signum() < 0 || exponent.bitLength() > Integer.SIZE - 1) {
            throw new ExactRangeExceeded("nothing is built at a power of " + exponent);
        }
        return exponent.intValueExact();
    }

    /**
     * Whether {@code whole × 2^twos × 5^fives} is a whole number the host holds, asked before it is
     * built and by whoever wants to know without building it.
     *
     * <p>The one count, because two of them are how a question and the building that answers it come
     * apart: a value the first called writable would be one the second then refused. It is under the
     * truth rather than over it, a factor of five counted as two bits where it is nearer two and a
     * third, so nothing the host would have held is refused here and what the under-count lets through
     * is refused by the host and translated where it is caught. The exponents are held wider than a
     * long, since a sum of an exponent and a scale need not fit one.
     */
    static boolean writable(BigInteger whole, BigInteger twos, BigInteger fives) {
        BigInteger bits = BigInteger.valueOf(whole.abs().bitLength()).add(twos).add(fives.shiftLeft(1));
        return bits.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) <= 0;
    }

    /**
     * A count of bits as the host takes one, and the shortage of room where it is past what the host
     * counts.
     *
     * <p>A bit length and a working width are both {@code int}, so a count made of two of them is an
     * {@code int} by default and wraps in silence, and what a wrapped count does is not refuse but
     * answer: a negative shift shifts the other way. The counts an instrument forms go through here.
     * It is the run's shortage rather than a value refused, because what these count is an instrument.
     */
    static int bitsTheHostAddresses(long bits) {
        if (bits > Integer.MAX_VALUE) {
            throw new ExactRoomExceeded("no room for a whole number of " + bits + " bits");
        }
        return (int) bits;
    }

    /** {@code 2^twos × 5^fives}, both exponents being non-negative. */
    static BigInteger powers(long twos, long fives) {
        return built(BigInteger.ONE, BigInteger.valueOf(twos), BigInteger.valueOf(fives));
    }

    /** {@code whole × 2^twos × 5^fives}, both exponents being at least nought. What this builds is
     *  the answer's own digits, which is the one thing a narrowing is always allowed to ask for.
     *
     *  @throws ExactRangeExceeded where no whole number the host holds is that number */
    static BigInteger built(BigInteger whole, BigInteger twos, BigInteger fives) {
        int byTwos = buildable(twos);
        int byFives = buildable(fives);
        if (!writable(whole, twos, fives)) {
            throw new ExactRangeExceeded("no whole number the host holds is a whole number of "
                    + whole.bitLength() + " bits times two to the " + twos + " times five to the " + fives);
        }
        BigInteger shifted = whole.shiftLeft(byTwos);
        return byFives == 0 ? shifted : shifted.multiply(FIVE.pow(byFives));
    }

    /**
     * What a whole number the host had no range for becomes: the answer has no representation.
     *
     * <p>A failure of this arithmetic already is one, and passes through unchanged.
     */
    static ExactFailure hostLimit(ArithmeticException thrown) {
        return thrown instanceof ExactFailure failure ? failure
                : new ExactRangeExceeded("no whole number that size is held: " + thrown.getMessage());
    }

    /** What the host's refusal of a whole number becomes inside an instrument: a shortage of room. */
    static ExactFailure hostShortage(ArithmeticException thrown, String what) {
        return thrown instanceof ExactFailure failure ? failure
                : new ExactRoomExceeded("no room " + what + ": " + thrown.getMessage());
    }
}
