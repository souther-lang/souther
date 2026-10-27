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
 * floating point is a rank for which the rows nearly fix them. Where the exact arithmetic gives out
 * the space is not known, and says so ({@link #known}).
 */
final class ExactSpan {

    private final int places;
    private final List<ExactRatio[]> held = new ArrayList<>();
    private final List<Integer> pivots = new ArrayList<>();
    private boolean known = true;

    ExactSpan(int places) {
        this.places = places;
    }

    /** Whether every vector was taken in exactly. Where not, no answer about the span is one. */
    boolean known() {
        return known;
    }

    /** The space the vectors so far and {@code vector} span. */
    void add(ExactRatio[] vector) {
        if (!known) {
            return;
        }
        ExactRatio[] reduced = vector.clone();
        for (int each = 0; each < held.size(); each++) {
            ExactRatio coef = reduced[pivots.get(each)];
            if (!coef.isZero() && !take(reduced, coef, held.get(each))) {
                return;
            }
        }
        int pivot = firstNonZero(reduced);
        if (pivot < 0) {
            return;
        }
        ExactRatio[] normalised = new ExactRatio[places];
        ExactRatio by = reduced[pivot];
        for (int at = 0; at < places; at++) {
            ExactRatio divided = reduced[at].dividedBy(by).orNull();
            if (divided == null) {
                known = false;
                return;
            }
            normalised[at] = divided;
        }
        for (ExactRatio[] other : held) {
            ExactRatio coef = other[pivot];
            if (!coef.isZero() && !take(other, coef, normalised)) {
                return;
            }
        }
        held.add(normalised);
        pivots.add(pivot);
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
                known = false;
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
