package souther.compiler.partition;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.Set;

/**
 * The whole numbers one number may still be, read off statements of it alone: those between two
 * ends, either of which may be missing, but for the ones held out.
 *
 * <p>Exactly those, and not a run around them. A run has no hole in it, so a value taken from the
 * run of {@code n /= 0} may be the very one held out, and that value failing says nothing of the
 * rest. Here what is held out is held out, and {@link #one} answers with a value that is left
 * wherever one is.
 *
 * @param least the least, or null where they run down without end
 * @param most  the greatest, or null where they run up without end
 * @param holes the values between the two that are held out
 */
record WholeNumbersLeft(BigInteger least, BigInteger most, Set<BigInteger> holes) {

    /** Every whole number. */
    static final WholeNumbersLeft EVERY = new WholeNumbersLeft(null, null, Set.of());

    /** No whole number. */
    private static final WholeNumbersLeft NONE =
            new WholeNumbersLeft(BigInteger.ONE, BigInteger.ZERO, Set.of());

    WholeNumbersLeft {
        holes = Set.copyOf(holes);
    }

    /** The whole numbers in {@code run} — or null where an end of it is no number. */
    static WholeNumbersLeft of(NumericDomain.Bounds run) {
        BigInteger least = null;
        BigInteger most = null;
        if (run.min() != null) {
            ExactRatio at = numberAt(run.min());
            if (at == null || !(at.ceiling() instanceof ExactAnswer.Held<BigInteger>(
                    BigInteger up))) {
                return null;
            }
            least = !run.min().inclusive() && at.isWhole() ? up.add(BigInteger.ONE) : up;
        }
        if (run.max() != null) {
            ExactRatio at = numberAt(run.max());
            if (at == null || !(at.floor() instanceof ExactAnswer.Held<BigInteger>(
                    BigInteger down))) {
                return null;
            }
            most = !run.max().inclusive() && at.isWhole() ? down.subtract(BigInteger.ONE) : down;
        }
        return new WholeNumbersLeft(least, most, Set.of());
    }

    private static ExactRatio numberAt(Endpoint end) {
        return end.at() instanceof Count count ? count.exactly() : null;
    }

    /**
     * What is left of these where {@code weight·n + constant} stands as {@code rel} says to
     * nought — or null where the arithmetic cannot say.
     */
    WholeNumbersLeft meeting(ExactRatio weight, ExactRatio constant, Rel rel) {
        if (weight.isZero()) {
            return rel.holds(constant.signum()) ? this : NONE;
        }
        if (!(constant.negated().dividedBy(weight) instanceof ExactAnswer.Held<ExactRatio>(
                ExactRatio at))
                || !(at.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger down))
                || !(at.ceiling() instanceof ExactAnswer.Held<BigInteger>(BigInteger up))) {
            return null;
        }
        // Weighed below nought, the number stands to the value the other way round.
        return switch (weight.signum() < 0 ? rel.turned() : rel) {
            case LT -> below(up.subtract(BigInteger.ONE));
            case LE -> below(down);
            case GT -> above(down.add(BigInteger.ONE));
            case GE -> above(up);
            case EQ -> at.isWhole() ? above(up).below(up) : NONE;
            case NE -> at.isWhole() ? without(up) : this;
        };
    }

    private WholeNumbersLeft below(BigInteger end) {
        return new WholeNumbersLeft(least, most == null ? end : most.min(end), holes);
    }

    private WholeNumbersLeft above(BigInteger end) {
        return new WholeNumbersLeft(least == null ? end : least.max(end), most, holes);
    }

    private WholeNumbersLeft without(BigInteger value) {
        Set<BigInteger> out = new HashSet<>(holes);
        out.add(value);
        return new WholeNumbersLeft(least, most, out);
    }

    /**
     * One of these, or null where none is left: the one nearest nought, and of two as near, the
     * one above it.
     *
     * <p>The first of these in one order of every whole number, which does not turn on these. So
     * a statement taken in later moves it only where it leaves it out: the first of some numbers
     * is the first of any of them that still hold it. Taking the least wherever there is a least
     * would not be that, since a bound found below then puts the value at the bound though the
     * one taken before is still left — and a value at a bound is where the numbers after it are
     * held tightest.
     *
     * <p>Only the values held out are ever passed over, so this looks at no more than one value
     * past them on each side.
     */
    BigInteger one() {
        if (least != null && most != null && least.compareTo(most) > 0) {
            return null;
        }
        BigInteger from = least != null && least.signum() > 0 ? least
                : most != null && most.signum() < 0 ? most : BigInteger.ZERO;
        for (BigInteger away = BigInteger.ZERO; ; away = away.add(BigInteger.ONE)) {
            BigInteger above = from.add(away);
            BigInteger below = from.subtract(away);
            boolean aboveLeft = holds(above);
            boolean belowLeft = holds(below);
            if (!aboveLeft && !belowLeft) {
                return null;
            }
            if (aboveLeft && !holes.contains(above)) {
                return above;
            }
            if (belowLeft && !holes.contains(below)) {
                return below;
            }
        }
    }

    /** Whether {@code value} lies between the two ends, held out or not. */
    private boolean holds(BigInteger value) {
        return (least == null || value.compareTo(least) >= 0)
                && (most == null || value.compareTo(most) <= 0);
    }
}
