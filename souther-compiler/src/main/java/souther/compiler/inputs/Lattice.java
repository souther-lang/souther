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
 * <p>The ends of a run are exact and never written out: a point is held as an end, a count of
 * steps from it, and, where the end is no point of the grid ({@code 1/3}), which way it is moved
 * onto the grid first ({@link Snap}). A point moved onto the grid is within a step of the end it
 * was moved from, and that is all two such points are compared by: the answer is given where it
 * holds whatever the exact places are, and is null where it does not. A caller reads null as "not
 * shown", never as either answer.
 */
final class Lattice {

    private static final ExactRatio FINEST_STEP = ExactRatio.of(new BigDecimal(BigInteger.ONE,
            Integer.MAX_VALUE));

    private Lattice() {
    }

    /** How an end that is no point of the grid is moved onto it. */
    enum Snap {
        /** The end is a point of the grid. */
        NONE,
        /** To the least point above the end. */
        UP,
        /** To the greatest point below the end. */
        DOWN
    }

    /**
     * A point of the grid: {@code end}, moved onto the grid as {@code snap} says, and then by
     * {@code steps} of the grid's step. A whole term's points have no steps, being whole numbers
     * held as they are.
     */
    record Point(ExactRatio end, int steps, Snap snap) {}

    /** Whether the number {@code at} is a value of a term spaced {@code spacing}. */
    static boolean holds(Granularity spacing, ExactRatio at) {
        return spacing == Granularity.DISCRETE ? at.isWhole() : at.fitsWrittenDecimal();
    }

    /**
     * The least point of the grid in the run that starts at {@code lower}, or null where the run
     * has none a whole term could take.
     */
    static Point least(Granularity spacing, ExactCut lower) {
        if (spacing == Granularity.DISCRETE) {
            BigInteger whole = lower.inclusive() ? lower.at().ceiling().orNull()
                    : lower.at().floor().map(below -> below.add(BigInteger.ONE)).orNull();
            return whole == null ? null : new Point(ExactRatio.of(whole), 0, Snap.NONE);
        }
        if (!lower.at().fitsWrittenDecimal()) {
            return new Point(lower.at(), 0, Snap.UP);
        }
        return new Point(lower.at(), lower.inclusive() ? 0 : 1, Snap.NONE);
    }

    /**
     * The greatest point of the grid in the run that ends at {@code upper}, or null where the run
     * has none a whole term could take.
     */
    static Point greatest(Granularity spacing, ExactCut upper) {
        if (spacing == Granularity.DISCRETE) {
            BigInteger whole = upper.inclusive() ? upper.at().floor().orNull()
                    : upper.at().ceiling().map(above -> above.subtract(BigInteger.ONE)).orNull();
            return whole == null ? null : new Point(ExactRatio.of(whole), 0, Snap.NONE);
        }
        if (!upper.at().fitsWrittenDecimal()) {
            return new Point(upper.at(), 0, Snap.DOWN);
        }
        return new Point(upper.at(), upper.inclusive() ? 0 : -1, Snap.NONE);
    }

    /**
     * How {@code one} stands to {@code other} on the grid: negative where it is below, nought
     * where they are the one point, or null where the places the ends are moved from leave it
     * open.
     *
     * <p>A point is its end plus a number of steps, and the move onto the grid adds something
     * strictly between nought and a step toward the side it goes. So the difference of two points
     * is the difference of the ends plus a number of steps held between two whole numbers of
     * them, and the sign is told where the ends are far enough apart for that to settle it. An end
     * too far for the difference to be held is far more than any steps could make up.
     */
    static Integer compare(Point one, Point other) {
        long steps = (long) one.steps() - other.steps();
        int ends = one.end().compareTo(other.end());
        if (ends == 0) {
            return Long.signum(steps + moved(one.snap()) - moved(other.snap()));
        }
        ExactRatio apart = one.end().minus(other.end()).orNull();
        if (apart == null) {
            return ends;
        }
        boolean exact = one.snap() == Snap.NONE && other.snap() == Snap.NONE;
        long least = steps + (exact ? 0 : lowest(one.snap()) - highest(other.snap()));
        long greatest = steps + (exact ? 0 : highest(one.snap()) - lowest(other.snap()));
        Integer fromLeast = against(apart, least);
        Integer fromGreatest = against(apart, greatest);
        if (fromLeast == null || fromGreatest == null) {
            return null;
        }
        if (fromLeast > 0 || (fromLeast == 0 && !exact)) {
            return 1;
        }
        if (fromGreatest < 0 || (fromGreatest == 0 && !exact)) {
            return -1;
        }
        return exact ? 0 : null;
    }

    /** The sign of {@code apart} plus {@code steps} of the finest step, or null if not held. */
    private static Integer against(ExactRatio apart, long steps) {
        ExactRatio wide = steps == 0 ? ExactRatio.ZERO
                : FINEST_STEP.times(ExactRatio.of(-steps)).orNull();
        return wide == null ? null : Integer.signum(apart.compareTo(wide));
    }

    /** How many steps an end moves by when it is the same end as another's. */
    private static int moved(Snap snap) {
        return snap == Snap.UP ? 1 : 0;
    }

    /** The least of what the move onto the grid adds, in steps: a bound it never reaches. */
    private static int lowest(Snap snap) {
        return snap == Snap.DOWN ? -1 : 0;
    }

    /** The greatest of what the move onto the grid adds, in steps: a bound it never reaches. */
    private static int highest(Snap snap) {
        return snap == Snap.UP ? 1 : 0;
    }
}
