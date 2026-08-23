package souther.compiler.observe;

/**
 * How much of a measure was actually measured.
 *
 * <p>A measure that could not read everything it needed must not be reported as if it had. Saying
 * "no example uses this case" when the rows that would have used it could not be classified is a
 * false positive, and a false positive in an adequacy report is worse than a missing number: it sends
 * the author to write a row that already exists.
 *
 * <p><b>A word for a document, and nothing the compiler decides anything by.</b> What a measure
 * came to is {@code souther.compiler.query.Measurement}, which has five states; these are the four
 * words a report writes them under, and the projection between the two lives in one place
 * ({@code souther.compiler.report.ReportMeasurement}).
 *
 * <p>It used to be the compiler's own answer as well, which made it a lattice — and a lattice
 * element is the join of whatever was thrown away to reach it. It had a {@code counted()} for
 * readers asking whether there was a number and an {@code and()} for parents folding their children
 * into one word; both are gone, because a measurement is asked what it is and a parent unions what
 * its parts went without (issue #953).
 *
 * <p>Which of those two it is, is the distinction a reader acts on. {@link #NOT_APPLICABLE} asks
 * nothing of anybody: there is nothing here for the measure to be about and no row could change
 * that. {@link #NOT_MEASURED} says what to do: the measure could have been made and was not. They
 * were one word once, and every reader that had to tell them apart rebuilt the difference out of
 * that measure's own reasons — which meant knowing each measure's reasons to read any of them, and
 * meant a measure whose reasons nobody had in mind was read as whichever the rebuild favoured.
 *
 * <p>Why in particular is still the measure's own. Which reasons a measure can have is that measure's
 * business; that it has one wherever there is no number, and none wherever there is, is the same
 * everywhere.
 *
 * <p>These are the compiler's words and not the report's. The report writes {@code not applicable}
 * and {@code not measured} (spec §example-report-vocabulary), and the JSON form writes
 * {@code unavailable} for both with the reason beside it — a projection each renderer makes, so that
 * naming a state here does not change what a document says.
 */
public enum MeasurementStatus {

    /** Everything this measure reads was readable. A gap is a real gap. */
    COMPLETE,

    /** Something this measure reads was unreadable, so a gap may not be one. */
    PARTIAL,

    /** Nothing here for the measure to be about, for a reason the measure gives. */
    NOT_APPLICABLE,

    /** It could have been made and was not, for a reason the measure gives. */
    NOT_MEASURED
}
