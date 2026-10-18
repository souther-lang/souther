package souther.compiler.inputs;

import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;

import java.math.BigDecimal;
import java.math.BigInteger;

/**
 * The values a term can take, as the points of a grid, and where a run of numbers lies on it.
 *
 * <p>An {@code Int} takes the whole numbers, a step of one apart. A {@code Decimal} takes the
 * decimals a model can write, which are the multiples of the finest step there is: its scale is
 * thirty-two bits ({@link ExactRatio#fitsWrittenDecimal}). So a run of numbers an end of which is
 * left out holds no value between that end and the one beside it on the grid, and "some value
 * below this one" is a question about where the grid's points are, not about the numbers.
 *
 * <p>The ends of a run are exact and never written out: a point is held as an end and a count of
 * steps from it ({@link Point}), because the end moved by a step is a number with as many digits as
 * the scale has places. Two points are compared by how far apart their ends are, and an end that
 * is not on the grid ({@code 1/3}) is a point nothing here can place, which is answered with null
 * and read by every caller as "not shown".
 */
final class Lattice {

    private static final ExactRatio FINEST_STEP = ExactRatio.of(new BigDecimal(BigInteger.ONE,
            Integer.MAX_VALUE));

    private Lattice() {
    }

    /**
     * A point of the grid: {@code end} moved by {@code steps} of the grid's step. A whole term's
     * points have no steps, being whole numbers held as they are.
     */
    record Point(ExactRatio end, int steps) {}

    /** Whether the number {@code at} is a value of a term spaced {@code spacing}. */
    static boolean holds(Granularity spacing, ExactRatio at) {
        return spacing == Granularity.DISCRETE ? at.isWhole() : at.fitsWrittenDecimal();
    }

    /**
     * The least point of the grid in the run that starts at {@code lower}, or null where that is
     * not worked out.
     */
    static Point least(Granularity spacing, ExactCut lower) {
        if (spacing == Granularity.DISCRETE) {
            BigInteger whole = lower.inclusive() ? lower.at().ceiling().orNull()
                    : lower.at().floor().map(below -> below.add(BigInteger.ONE)).orNull();
            return whole == null ? null : new Point(ExactRatio.of(whole), 0);
        }
        if (!lower.at().fitsWrittenDecimal()) {
            return null;
        }
        return new Point(lower.at(), lower.inclusive() ? 0 : 1);
    }

    /**
     * The greatest point of the grid in the run that ends at {@code upper}, or null where that is
     * not worked out.
     */
    static Point greatest(Granularity spacing, ExactCut upper) {
        if (spacing == Granularity.DISCRETE) {
            BigInteger whole = upper.inclusive() ? upper.at().floor().orNull()
                    : upper.at().ceiling().map(above -> above.subtract(BigInteger.ONE)).orNull();
            return whole == null ? null : new Point(ExactRatio.of(whole), 0);
        }
        if (!upper.at().fitsWrittenDecimal()) {
            return null;
        }
        return new Point(upper.at(), upper.inclusive() ? 0 : -1);
    }

    /**
     * How {@code one} stands to {@code other} on the grid: negative where it is below, nought
     * where they are the one point.
     *
     * <p>The ends are values of the grid, so two that differ are at least a step apart, and the
     * difference is a number a step or two wide whenever it is held at all; one too wide to be
     * held is far more than the steps moving the ends could make up.
     */
    static int compare(Point one, Point other) {
        int steps = one.steps() - other.steps();
        int ends = one.end().compareTo(other.end());
        if (ends == 0) {
            return Integer.signum(steps);
        }
        ExactRatio apart = (ends < 0 ? other.end().minus(one.end()) : one.end().minus(other.end()))
                .orNull();
        if (ends < 0) {
            // one - other is minus the difference, plus the steps.
            if (steps <= 0) {
                return -1;
            }
            return apart == null ? -1 : stepsWide(steps).compareTo(apart);
        }
        if (steps >= 0) {
            return 1;
        }
        return apart == null ? 1 : apart.compareTo(stepsWide(-steps));
    }

    private static ExactRatio stepsWide(int steps) {
        return FINEST_STEP.times(ExactRatio.of(steps)).orNull();
    }
}
