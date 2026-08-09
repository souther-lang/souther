package souther.compiler.query;

import souther.compiler.observe.MeasurementStatus;

/**
 * The one thing every measure keeps: a measure with no number says why, and a measure with a number
 * has nothing to say.
 *
 * <p>Checked where the value is built rather than where it is read. A measure whose reason went
 * missing was read back from whatever else was to hand — the row count, the kind of behavior, the
 * declaration — and every one of those is a different question that happens to correlate. What each
 * reason can be is the measure's own business, so this holds the shape and not the words.
 */
final class Unavailable {

    static void check(MeasurementStatus status, Object reason) {
        if (status.counted() == (reason != null)) {
            throw new IllegalArgumentException(status + " with " + reason);
        }
    }

    private Unavailable() {}
}
