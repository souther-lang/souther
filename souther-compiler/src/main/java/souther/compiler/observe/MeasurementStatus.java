package souther.compiler.observe;

/**
 * How much of a measure was actually measured.
 *
 * <p>A measure that could not read everything it needed must not be reported as if it had. Saying
 * "no example uses this case" when the rows that would have used it could not be classified is a
 * false positive, and a false positive in an adequacy report is worse than a missing number: it sends
 * the author to write a row that already exists.
 *
 * <p>The three are read the same way everywhere. Only {@link #COMPLETE} may raise a missing-coverage
 * diagnostic; {@link #PARTIAL} reports what it saw and says it could not decide; {@link #UNAVAILABLE}
 * has no number to show at all.
 */
public enum MeasurementStatus {

    /** Everything this measure reads was readable. A gap is a real gap. */
    COMPLETE,

    /** Something this measure reads was unreadable, so a gap may not be one. */
    PARTIAL,

    /** The measure could not run here at all — an injected behavior has no branches to cover. */
    UNAVAILABLE;

    /** The weaker of two statuses, for a measure assembled from several sources. */
    public MeasurementStatus and(MeasurementStatus other) {
        if (this == UNAVAILABLE || other == UNAVAILABLE) {
            return UNAVAILABLE;
        }
        return this == PARTIAL || other == PARTIAL ? PARTIAL : COMPLETE;
    }
}
