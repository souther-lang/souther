package souther.compiler.check;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;

/**
 * A way of rounding a number to a whole one, as what a comparison of the rounded number states of
 * the number before it was rounded.
 *
 * <p>One per case of the library's rounding policy, and which case is which is held to the library
 * where the fact naming the policy is bound ({@link OperationFactBinder}). What each does is the
 * run time's: {@code DOWN} drops the fraction toward nought, {@code FLOOR} toward minus infinity,
 * and the three halves round to the nearer whole number and part at an exact half.
 *
 * <p><b>One question per way of rounding.</b> Where the rounded number is at least a whole number
 * {@code k} is a line on the number before rounding, at {@code k}, at {@code k - 1} or at a half
 * below {@code k}, and the line is or is not part of the stretch. Every other relation to {@code k}
 * is that one asked again at {@code k} or {@code k + 1} and denied
 * ({@link ConstantComparison#ofAWholeNumber}), so the line is the whole of what is particular to a
 * way of rounding.
 */
public enum WholeRounding {

    HALF_UP,
    HALF_EVEN,
    HALF_DOWN,
    UP,
    DOWN,
    CEILING,
    FLOOR;

    /**
     * The whole number {@code x} rounds to this way, or null where the exact arithmetic cannot
     * hold the whole numbers either side of it.
     *
     * <p>Between the two whole numbers either side of {@code x}, and {@code x} itself where it is
     * one: toward minus infinity, toward plus infinity, toward nought, away from it, and for the
     * three halves the nearer of the two, an exact half going where its rule sends it.
     */
    public BigInteger of(ExactRatio x) {
        if (!(x.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger below))
                || !(x.ceiling() instanceof ExactAnswer.Held<BigInteger>(BigInteger above))) {
            return null;
        }
        if (below.equals(above)) {
            return below;
        }
        ExactRatio past = x.minus(ExactRatio.of(below)).orNull();
        if (past == null) {
            return null;
        }
        boolean positive = x.signum() > 0;
        int half = past.compareTo(ExactRatio.of(BigInteger.ONE, BigInteger.TWO));
        return switch (this) {
            case FLOOR -> below;
            case CEILING -> above;
            case DOWN -> positive ? below : above;
            case UP -> positive ? above : below;
            case HALF_UP -> half != 0 ? (half > 0 ? above : below) : (positive ? above : below);
            case HALF_DOWN -> half != 0 ? (half > 0 ? above : below) : (positive ? below : above);
            case HALF_EVEN -> half != 0 ? (half > 0 ? above : below)
                    : (below.testBit(0) ? above : below);
        };
    }

    /**
     * What the number before rounding stands to exactly where its rounding is at least {@code k}.
     *
     * <p>Toward nought and away from it part at the sign of {@code k}: a number above minus one
     * drops to nought, so the rounding toward nought is at least nought from just above minus one,
     * and at least one only from one. An exact half goes where its own rule sends it: up to
     * {@code k} for {@code HALF_UP} above nought and for {@code HALF_DOWN} at or below it, and for
     * {@code HALF_EVEN} where {@code k} is even.
     */
    ConstantComparison.Against atLeast(BigInteger k) {
        boolean positive = k.signum() > 0;
        return switch (this) {
            case FLOOR -> from(k);
            case CEILING -> above(k.subtract(BigInteger.ONE));
            case DOWN -> positive ? from(k) : above(k.subtract(BigInteger.ONE));
            case UP -> positive ? above(k.subtract(BigInteger.ONE)) : from(k);
            case HALF_UP -> atAHalfBelow(k, positive);
            case HALF_DOWN -> atAHalfBelow(k, !positive);
            case HALF_EVEN -> atAHalfBelow(k, !k.testBit(0));
        };
    }

    private static ConstantComparison.Against from(BigInteger line) {
        return new ConstantComparison.Against(Rel.GE, ExactRatio.of(line));
    }

    private static ConstantComparison.Against above(BigInteger line) {
        return new ConstantComparison.Against(Rel.GT, ExactRatio.of(line));
    }

    /** The number at or above a half below {@code k}, the half itself where it rounds up. */
    private static ConstantComparison.Against atAHalfBelow(BigInteger k, boolean roundsUp) {
        return new ConstantComparison.Against(roundsUp ? Rel.GE : Rel.GT,
                ExactRatio.of(k.shiftLeft(1).subtract(BigInteger.ONE), BigInteger.TWO));
    }
}
