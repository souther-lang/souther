package souther.exact;

import org.jspecify.annotations.Nullable;

import java.math.BigInteger;
import java.math.RoundingMode;

import static souther.exact.ExactOrder.BRACKET_BITS;

/**
 * The whole number a value comes to at a scale, by a rounding policy.
 *
 * <p>The scale goes to the exponents, not the digits. A decimal of {@code scale} places is a whole number
 * over {@code 10^scale}, so what is asked for is the whole number the value rounds to when multiplied by
 * that power — and multiplying by it moves the two exponents. So the rounding is done on the factored
 * value, and never on a decimal built and then rounded: what a value's own exponents say has nothing to
 * do with how large the answer is, and a value made of a power of two over a power of five that all but
 * cancel stands near one, where spelling it out first asks for digits the answer does not have and no
 * machine holds. Which is the same reason the order is answered from brackets, and the brackets are what
 * this reads too.
 */
final class ExactRounding {

    /** The denominator of half of one, which is what a remainder is compared against to say which side
     *  of half way between two whole numbers a value stands. */
    private static final BigInteger HALVES = BigInteger.valueOf(2);

    private ExactRounding() {
    }

    /**
     * The whole number {@code of × 10^scale} rounds to by {@code towards}, which is the unscaled value of
     * the value at that scale.
     *
     * <p>Multiplying by the power of ten adds the scale to both exponents, and the sum is held wider than
     * an exponent is: a value whose own exponent is at the end of its range has an ordinary answer at an
     * ordinary scale, so an intermediate here is not held to what the answer is allowed to be.
     *
     * <p>Two shapes are read off the exponents rather than bracketed, because a bracket can never say that
     * a value <i>is</i> a whole number or <i>is</i> exactly half of one, and the policies part company at
     * exactly half. In lowest terms with no two and no five left beside the fraction, the value is a whole
     * number exactly where the denominator is one and both exponents have reached nought, and it is half
     * of one exactly where the same holds of twice it.
     *
     * @throws IllegalArgumentException where the value is not a whole number at that scale and the policy
     *         is {@link RoundingMode#UNNECESSARY}, which names no rounding
     */
    static BigInteger roundedTimesTenTo(ExactParts of, int scale, RoundingMode towards) {
        if (of.isZero()) {
            return BigInteger.ZERO;
        }
        try {
            return rounded(of, scale, towards);
        } catch (ArithmeticException e) {
            throw ExactPowers.hostLimit(e);
        }
    }

    private static BigInteger rounded(ExactParts of, int scale, RoundingMode towards) {
        BigInteger byTwos = atTenTo(of.twos(), scale);
        BigInteger byFives = atTenTo(of.fives(), scale);
        BigInteger magnitude = of.numerator().abs();
        boolean overOne = of.denominator().equals(BigInteger.ONE);
        if (overOne && byTwos.signum() >= 0 && byFives.signum() >= 0) {
            return signedLike(of, ExactPowers.built(magnitude, byTwos, byFives));
        }
        // Twice the value, so that one whole number carries both which two it stands between and which
        // side of half of the way it stands: its half is the one, its last bit the other.
        BigInteger byTwiceTheTwos = byTwos.add(BigInteger.ONE);
        if (overOne && byTwiceTheTwos.signum() >= 0 && byFives.signum() >= 0) {
            return roundedFrom(of,
                    ExactPowers.built(magnitude, byTwiceTheTwos, byFives).shiftRight(1), 0, towards);
        }
        BigInteger quickly = roundedFromBracketsAt(
                of, byTwiceTheTwos, byFives, towards, BRACKET_BITS);
        if (quickly != null) {
            return quickly;
        }
        // The bracket left two whole numbers in it, so the value stands close to half of the way between
        // them. Where the powers can be written down, writing them down answers exactly, at whatever
        // closeness the value happens to have, which is the shape no width settled on beforehand reaches.
        BigInteger exactly = roundedExactly(of, byTwos, byFives, towards);
        if (exactly != null) {
            return exactly;
        }
        // Which way a value rounds is where it stands against half of the way between two whole numbers,
        // and that is an order, so it is refined by what refines the order and for the same reason.
        return ExactOrder.asWideAsItTakes(
                width -> roundedFromBracketsAt(of, byTwiceTheTwos, byFives, towards, width),
                () -> "round a value");
    }

    /**
     * The whole number a value rounds to at those exponents, read off one division of the value written
     * out.
     *
     * <p>The whole part is the quotient, and where the value stands against half of the way is where the
     * remainder stands against half the denominator — one fraction against another, answered by the same
     * walk the order uses. Nothing is doubled on top of that: doubling the remainder would ask for a
     * number a bit larger than one already stored, which is the bit the host does not have at its own end.
     */
    private static @Nullable BigInteger roundedExactly(
            ExactParts of, BigInteger byTwos, BigInteger byFives, RoundingMode towards) {
        BigInteger @Nullable [] written = ExactOrder.allWrittenOut(
                ExactOrder.bitsAWritingIsWorth(ExactOrder.storedBits(of)),
                new ExactOrder.ToWriteOut(of.numerator().abs(), byTwos, byFives),
                new ExactOrder.ToWriteOut(of.denominator(), byTwos.negate(), byFives.negate()));
        if (written == null) {
            return null;
        }
        BigInteger up = written[0];
        BigInteger down = written[1];
        BigInteger[] whole = up.divideAndRemainder(down);
        if (whole[1].signum() == 0) {
            return signedLike(of, whole[0]);
        }
        return roundedFrom(of, whole[0],
                ExactOrder.comparedAsFractions(whole[1], down, BigInteger.ONE, HALVES), towards);
    }

    /** The whole number a value rounds to as far as a bracket of {@code width} bits settles it, and null
     *  where the bracket holds two of them. */
    private static @Nullable BigInteger roundedFromBracketsAt(ExactParts of,
            BigInteger byTwiceTheTwos, BigInteger byFives, RoundingMode towards, int width) {
        ExactOrder.Bracketed twice = ExactOrder.bracketed(of, byTwiceTheTwos, byFives, width);
        BigInteger least = flooredFraction(twice.low(), BigInteger.ONE, twice.shift());
        BigInteger most = flooredFraction(twice.high(), BigInteger.ONE, twice.shift());
        return least.equals(most)
                ? roundedFrom(of, least.shiftRight(1), least.testBit(0) ? 1 : -1, towards)
                : null;
    }

    /**
     * Which of {@code whole} and the next one up the value rounds to, the value standing
     * {@code againstHalf} of the way between them and neither being reached exactly.
     *
     * <p>Every policy but one reads the sign and that standing and nothing else. At exactly half of the
     * way the two neighbours are this whole number and the next, and the policy that takes the even one
     * takes whichever of those is even.
     *
     * <p>{@link RoundingMode#UNNECESSARY} asks for no rounding at all, and is reached only where rounding
     * is what the value needs — a value exact at the scale asked for is answered before this. So it
     * refuses the way a caller's mistake is refused, and not as {@link ExactRangeExceeded}, which says a
     * number was too large.
     */
    private static BigInteger roundedFrom(
            ExactParts of, BigInteger whole, int againstHalf, RoundingMode towards) {
        boolean awayFromNought = switch (towards) {
            case UP -> true;
            case DOWN -> false;
            case CEILING -> of.signum() > 0;
            case FLOOR -> of.signum() < 0;
            case HALF_UP -> againstHalf >= 0;
            case HALF_DOWN -> againstHalf > 0;
            case HALF_EVEN -> againstHalf > 0 || (againstHalf == 0 && whole.testBit(0));
            case UNNECESSARY -> throw new IllegalArgumentException(
                    "this value is not the whole number asked for, and no rounding was named");
        };
        return signedLike(of, awayFromNought ? whole.add(BigInteger.ONE) : whole);
    }

    /** An exponent with a scale added, held wider than an exponent is — the scale reaches every value,
     *  so their sum is not bounded by what one of them is. */
    private static BigInteger atTenTo(long exponent, int scale) {
        return BigInteger.valueOf(exponent).add(BigInteger.valueOf(scale));
    }

    /**
     * {@code floor(up × 2^byBits / down)}, {@code up} being at least nought and {@code down} above it.
     *
     * <p>Exact, and nothing here is larger than the answer or than what it was handed. Moved up, what is
     * built is the answer's own digits. Moved down, the numerator comes down rather than the denominator
     * going up, so the distance comes out of a number that has it to give. Down by more bits than the
     * numerator has, the value is below one and the floor is nought, and the distance itself is one no
     * count of bits holds.
     */
    private static BigInteger flooredFraction(BigInteger up, BigInteger down, BigInteger byBits) {
        if (byBits.signum() >= 0) {
            return up.shiftLeft(ExactPowers.buildable(byBits)).divide(down);
        }
        BigInteger by = byBits.negate();
        if (by.compareTo(BigInteger.valueOf(up.bitLength())) > 0) {
            return BigInteger.ZERO;
        }
        return up.shiftRight(by.intValueExact()).divide(down);
    }

    private static BigInteger signedLike(ExactParts of, BigInteger magnitude) {
        return of.signum() < 0 ? magnitude.negate() : magnitude;
    }
}
