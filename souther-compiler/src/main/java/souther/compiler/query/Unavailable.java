package souther.compiler.query;

import souther.compiler.observe.MeasureReason;
import souther.compiler.observe.MeasurementStatus;

/**
 * The one thing every measure keeps: a measure with no number says why, the reason says which kind
 * of no-number it is, and a measure with a number has nothing to say.
 *
 * <p>Checked where the value is built rather than where it is read. A measure whose reason went
 * missing was read back from whatever else was to hand — the row count, the kind of behavior, the
 * declaration — and every one of those is a different question that happens to correlate.
 *
 * <p>The kinds are checked against each other and not only for presence. What each reason can be is
 * the measure's own business; that a reason and the status beside it are the same answer is not, and
 * a measure saying its arms do not apply while asking somebody to go and measure them is exactly the
 * confusion the two words were split to prevent.
 */
final class Unavailable {

    static void check(MeasurementStatus status, MeasureReason reason) {
        if (status.counted()) {
            if (reason != null) {
                throw new IllegalArgumentException(status + " with " + reason);
            }
            return;
        }
        if (reason == null) {
            throw new IllegalArgumentException(status + " with no reason");
        }
        if (reason.status() != status) {
            throw new IllegalArgumentException(status + " with " + reason + ", which is "
                    + reason.status());
        }
    }

    private Unavailable() {}
}
