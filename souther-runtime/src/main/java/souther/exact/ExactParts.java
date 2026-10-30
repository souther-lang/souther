package souther.exact;

import java.math.BigInteger;
import java.util.Objects;

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
 *
 * <p><b>A whole number a long holds is held as a long.</b> Nearly every number a model and the
 * constraint algebra make is a count, an amount or a decimal of a few digits, and a
 * {@code BigInteger} of one is two objects where a long is none. So each of the two whole numbers is
 * a long where a long holds it and a {@code BigInteger} where it does not, and which of the two it is
 * follows from the number alone: a number a long holds is never kept as a {@code BigInteger}, however
 * it was handed over. Equal parts are therefore one representation, and {@link #equals} and
 * {@link #hashCode} ask the fields.
 */
public final class ExactParts {

    /** The numerator where {@link #wideNumerator} is null. */
    private final long numerator;
    /** The denominator where {@link #wideDenominator} is null. */
    private final long denominator;
    /** The numerator where no long holds it, and null where one does. */
    private final BigInteger wideNumerator;
    /** The denominator where no long holds it, and null where one does. */
    private final BigInteger wideDenominator;
    private final long twos;
    private final long fives;

    /**
     * Parts with a nought below the line are no value, canonical or not, so none are made. What
     * the arithmetic forms below the line is a product of denominators it was handed and of a
     * divisor's numerator once nought is turned away, so it never forms one.
     *
     * @throws IllegalArgumentException where the denominator is nought
     */
    public ExactParts(BigInteger numerator, BigInteger denominator, long twos, long fives) {
        if (denominator.signum() == 0) {
            throw new IllegalArgumentException("parts of a value have no nought below the line");
        }
        boolean numeratorFits = fitsALong(numerator);
        boolean denominatorFits = fitsALong(denominator);
        this.numerator = numeratorFits ? numerator.longValue() : 0;
        this.denominator = denominatorFits ? denominator.longValue() : 0;
        this.wideNumerator = numeratorFits ? null : numerator;
        this.wideDenominator = denominatorFits ? null : denominator;
        this.twos = twos;
        this.fives = fives;
    }

    /**
     * The same parts, of two whole numbers a long holds.
     *
     * @throws IllegalArgumentException where the denominator is nought
     */
    public ExactParts(long numerator, long denominator, long twos, long fives) {
        if (denominator == 0) {
            throw new IllegalArgumentException("parts of a value have no nought below the line");
        }
        this.numerator = numerator;
        this.denominator = denominator;
        this.wideNumerator = null;
        this.wideDenominator = null;
        this.twos = twos;
        this.fives = fives;
    }

    public static final ExactParts ZERO = new ExactParts(0, 1, 0, 0);

    private static boolean fitsALong(BigInteger whole) {
        return whole.bitLength() < Long.SIZE;
    }

    /** The number above the line, at whatever width. A {@code BigInteger} is made of it where it is
     *  held as a long, so a step that can work in longs asks {@link #numeratorInALong} instead. */
    public BigInteger numerator() {
        return wideNumerator != null ? wideNumerator : BigInteger.valueOf(numerator);
    }

    /** The number below the line, at whatever width, as {@link #numerator} is. */
    public BigInteger denominator() {
        return wideDenominator != null ? wideDenominator : BigInteger.valueOf(denominator);
    }

    public long twos() {
        return twos;
    }

    public long fives() {
        return fives;
    }

    /** Whether a long holds both whole numbers, which is where {@link #numeratorInALong} and
     *  {@link #denominatorInALong} answer. */
    public boolean inLongs() {
        return wideNumerator == null && wideDenominator == null;
    }

    /** The number above the line, of parts whose numbers a long holds ({@link #inLongs}). */
    public long numeratorInALong() {
        if (wideNumerator != null) {
            throw new IllegalStateException("no long holds this numerator");
        }
        return numerator;
    }

    /** The number below the line, of parts whose numbers a long holds ({@link #inLongs}). */
    public long denominatorInALong() {
        if (wideDenominator != null) {
            throw new IllegalStateException("no long holds this denominator");
        }
        return denominator;
    }

    /**
     * Written out: {@link ExactArithmetic#compare} asks it first of every pair. The exponents are
     * compared before the integers, since two values that differ mostly differ there; a number held
     * as a long and one held wider are never equal, since a number a long holds is never held wider.
     */
    @Override
    public boolean equals(Object other) {
        return this == other || (other instanceof ExactParts parts
                && twos == parts.twos && fives == parts.fives
                && numerator == parts.numerator && denominator == parts.denominator
                && Objects.equals(wideNumerator, parts.wideNumerator)
                && Objects.equals(wideDenominator, parts.wideDenominator));
    }

    /** The hash a {@code BigInteger} of each number has, whichever way it is held, so that a value
     *  hashes as it did when both were {@code BigInteger}s. */
    @Override
    public int hashCode() {
        int hash = wideNumerator != null ? wideNumerator.hashCode() : hashOf(numerator);
        hash = 31 * hash + (wideDenominator != null ? wideDenominator.hashCode() : hashOf(denominator));
        hash = 31 * hash + Long.hashCode(twos);
        return 31 * hash + Long.hashCode(fives);
    }

    /** {@link BigInteger#hashCode} of {@code whole}: the magnitude's words from the most significant,
     *  each folded in times thirty-one, and the sign last. The magnitude is read unsigned, which the
     *  least long's is. */
    private static int hashOf(long whole) {
        long magnitude = Math.abs(whole);
        int high = (int) (magnitude >>> Integer.SIZE);
        int low = (int) magnitude;
        int hash = high != 0 ? 31 * high + low : low;
        return hash * Long.signum(whole);
    }

    @Override
    public String toString() {
        return "ExactParts[numerator=" + numerator() + ", denominator=" + denominator()
                + ", twos=" + twos + ", fives=" + fives + "]";
    }

    public boolean isZero() {
        return wideNumerator == null && numerator == 0;
    }

    /** Whether the number below the line is one. */
    public boolean overOne() {
        return wideDenominator == null && denominator == 1;
    }

    public int signum() {
        return wideNumerator != null ? wideNumerator.signum() : Long.signum(numerator);
    }
}
