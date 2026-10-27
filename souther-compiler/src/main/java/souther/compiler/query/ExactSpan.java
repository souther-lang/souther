package souther.compiler.query;

import souther.compiler.numeric.ExactRatio;

import java.util.ArrayList;
import java.util.List;

/**
 * The space the vectors added to it span, in exact arithmetic, and which axes of it they reach.
 *
 * <p>Kept fully reduced: each vector held has a pivot place, one at its pivot and nought at every
 * other vector's pivot. An axis is in the span exactly where the vector pivoted at it has nothing
 * but that one place — any other vector reaching it would have to leave the rest of that vector's
 * places cancelled, and the places left over are each another vector's pivot or nobody's.
 *
 * <p>Exact because what is asked is whether the weights are fixed, and a rank worked out in
 * floating point is a rank for which the rows nearly fix them. A vector the exact arithmetic gives
 * out on is not taken in and leaves the space as it was, so what the vectors taken in reach is
 * still reached; {@link #add} says it was left out.
 */
final class ExactSpan {

    private final int places;
    private List<ExactRatio[]> held = new ArrayList<>();
    private List<Integer> pivots = new ArrayList<>();

    ExactSpan(int places) {
        this.places = places;
    }

    /**
     * The space the vectors so far and {@code vector} span, or false where the exact arithmetic gave
     * out and the space is the one before.
     */
    boolean add(ExactRatio[] vector) {
        ExactRatio[] reduced = vector.clone();
        for (int each = 0; each < held.size(); each++) {
            ExactRatio coef = reduced[pivots.get(each)];
            if (!coef.isZero() && !take(reduced, coef, held.get(each))) {
                return false;
            }
        }
        int pivot = firstNonZero(reduced);
        if (pivot < 0) {
            return true;
        }
        ExactRatio[] normalised = new ExactRatio[places];
        ExactRatio by = reduced[pivot];
        for (int at = 0; at < places; at++) {
            ExactRatio divided = reduced[at].dividedBy(by).orNull();
            if (divided == null) {
                return false;
            }
            normalised[at] = divided;
        }
        List<ExactRatio[]> next = new ArrayList<>();
        for (ExactRatio[] other : held) {
            ExactRatio[] eliminated = other.clone();
            ExactRatio coef = eliminated[pivot];
            if (!coef.isZero() && !take(eliminated, coef, normalised)) {
                return false;
            }
            next.add(eliminated);
        }
        next.add(normalised);
        List<Integer> nextPivots = new ArrayList<>(pivots);
        nextPivots.add(pivot);
        held = next;
        pivots = nextPivots;
        return true;
    }

    /** Whether the axis of {@code place} is in the span, which is whether the vectors fix it. */
    boolean reaches(int place) {
        int row = pivots.indexOf(place);
        if (row < 0) {
            return false;
        }
        ExactRatio[] vector = held.get(row);
        for (int at = 0; at < places; at++) {
            if (at != place && !vector[at].isZero()) {
                return false;
            }
        }
        return true;
    }

    /** {@code from} less {@code coef} times {@code by}, written into {@code from}, or false
     *  where the exact arithmetic gave out. */
    private boolean take(ExactRatio[] from, ExactRatio coef, ExactRatio[] by) {
        for (int at = 0; at < places; at++) {
            ExactRatio scaled = by[at].times(coef).orNull();
            ExactRatio left = scaled == null ? null : from[at].minus(scaled).orNull();
            if (left == null) {
                return false;
            }
            from[at] = left;
        }
        return true;
    }

    private int firstNonZero(ExactRatio[] vector) {
        for (int at = 0; at < places; at++) {
            if (!vector[at].isZero()) {
                return at;
            }
        }
        return -1;
    }
}
