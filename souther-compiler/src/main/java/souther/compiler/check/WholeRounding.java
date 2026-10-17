package souther.compiler.check;

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
enum WholeRounding {

    HALF_UP(true),
    HALF_EVEN(true),
    HALF_DOWN(true),
    UP(false),
    DOWN(false),
    CEILING(false),
    FLOOR(false);

    private final boolean atAHalf;

    WholeRounding(boolean atAHalf) {
        this.atAHalf = atAHalf;
    }

    /**
     * Whether its lines are at a half: the number a statement is about is then the rounded number
     * taken twice, so that a line at {@code k - 1/2} is the whole number {@code 2k - 1}.
     */
    boolean linesAtAHalf() {
        return atAHalf;
    }

    /**
     * What the number before rounding — taken twice where {@link #linesAtAHalf} — stands to exactly
     * where its rounding is at least {@code k}.
     *
     * <p>Toward nought and away from it part at the sign of {@code k}: a number above minus one
     * drops to nought, so the rounding toward nought is at least nought from just above minus one,
     * and at least one only from one. An exact half goes where its own rule sends it: up to
     * {@code k} for {@code HALF_UP} above nought and for {@code HALF_DOWN} at or below it, and for
     * {@code HALF_EVEN} where {@code k} is even.
     */
    ConstantComparison.Against atLeast(BigInteger k) {
        BigInteger one = BigInteger.ONE;
        boolean positive = k.signum() > 0;
        return switch (this) {
            case FLOOR -> new ConstantComparison.Against(Rel.GE, k);
            case CEILING -> new ConstantComparison.Against(Rel.GT, k.subtract(one));
            case DOWN -> positive ? new ConstantComparison.Against(Rel.GE, k)
                    : new ConstantComparison.Against(Rel.GT, k.subtract(one));
            case UP -> positive ? new ConstantComparison.Against(Rel.GT, k.subtract(one))
                    : new ConstantComparison.Against(Rel.GE, k);
            case HALF_UP -> atAHalfBelow(k, positive);
            case HALF_DOWN -> atAHalfBelow(k, !positive);
            case HALF_EVEN -> atAHalfBelow(k, !k.testBit(0));
        };
    }

    /** Twice the number at or above twice {@code k} less one, the line itself where it rounds up. */
    private static ConstantComparison.Against atAHalfBelow(BigInteger k, boolean roundsUp) {
        return new ConstantComparison.Against(roundsUp ? Rel.GE : Rel.GT,
                k.shiftLeft(1).subtract(BigInteger.ONE));
    }
}
