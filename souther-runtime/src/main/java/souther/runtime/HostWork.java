package souther.runtime;

import java.math.BigDecimal;
import java.math.BigInteger;

/**
 * What one call into the host's arbitrary-precision arithmetic is paid for with, before it is made.
 *
 * <p>Counted in words of sixty-four bits, from how large the numbers are as they are held and as the
 * answer will be held, and never from time. Reading or writing a number is a piece of work a word,
 * multiplying two numbers is the words of one times the words of the other, as the schoolbook does
 * it, and building a power by squaring is its words times the squarings. The host does better than
 * the schoolbook on numbers of thousands of words, so what is paid is above what is done; it is a
 * count that is the same on every machine and grows the way the work does, and not a forecast.
 *
 * <p>A number past what the host builds — a whole number of more than {@link #MOST_BITS} bits — is
 * not paid for. The call refuses it, which is the answer the operation has for it, and paying for it
 * first would turn that answer into the evaluation running out.
 */
final class HostWork {

    /** The most bits a whole number the host builds has. */
    static final long MOST_BITS = Integer.MAX_VALUE;

    private HostWork() {}

    /** The bits {@code n} is held in. */
    static long bits(BigInteger n) {
        return n.bitLength();
    }

    /** The bits {@code d}'s digits are held in, whatever its scale. */
    static long bits(BigDecimal d) {
        return d.unscaledValue().bitLength();
    }

    /** The bits a power of ten {@code tens} digits long is held in: over three and a third a digit. */
    static long bitsOfTens(long tens) {
        long digits = Math.abs(tens);
        return digits > MOST_BITS ? MOST_BITS + 1 : digits * 3322 / 1000 + 1;
    }

    /** Whether a number of {@code bits} bits is one the host builds. */
    static boolean built(long bits) {
        return bits <= MOST_BITS;
    }

    static long words(long bits) {
        return bits / 64 + 1;
    }

    /** Reading and writing numbers of these sizes, a piece a word. */
    static long read(long... bits) {
        long pieces = 0;
        for (long each : bits) {
            pieces += words(each);
        }
        return pieces;
    }

    /** Multiplying, or dividing, a number of {@code a} bits by one of {@code b}. */
    static long product(long a, long b) {
        return words(a) * words(b);
    }

    /** Building a power {@code bits} bits long by squaring. */
    static long power(long bits) {
        long words = words(bits);
        return words * (64 - Long.numberOfLeadingZeros(words));
    }

    /**
     * Pays {@code pieces} to {@code checkpoint}, where every number the call will form has a size the
     * host builds; {@code largest} is the bits of the largest of them.
     */
    static void pay(WorkCheckpoint checkpoint, long largest, long pieces) {
        if (built(largest)) {
            checkpoint.spend(pieces);
        }
    }
}
