package souther.compiler.report;

import souther.compiler.observe.MeasureReason;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Measure;
import souther.compiler.query.Measurement;
import souther.compiler.query.WeakeningSet;

import java.util.Optional;

/**
 * One measurement as a document says it.
 *
 * <p>The only place {@link MeasurementStatus} is read. Everywhere else asks a measurement what it
 * is, which is what it can answer; a word is what a reader of a document is handed, and a word is
 * all this makes.
 *
 * <p><b>Written once because it is a policy.</b> Two renderers read every measure — one for a person
 * and one for a build — and a projection spelled at each of them is the same decision made twice, in
 * as many places as there are lines to print. That is how the compiler came to have a status per
 * measure and a second status beside one of them: what a word means was settled wherever a word was
 * needed.
 *
 * <p><b>The two state spaces are deliberately different sizes, and the projection loses nothing.</b>
 * A measurement nobody asked for and one that was started and could not be finished are two states
 * here and one word there. What tells them apart in a document is the weakening beside the word:
 *
 * <table>
 *   <caption>what a document carries, and what it means</caption>
 *   <tr><th>status</th><th>weakening</th><th>state</th></tr>
 *   <tr><td>{@code complete}</td><td>empty</td><td>{@link Measurement.Complete}</td></tr>
 *   <tr><td>{@code partial}</td><td>non-empty</td><td>{@link Measurement.Partial}</td></tr>
 *   <tr><td>{@code unavailable} / not applicable</td><td>empty</td>
 *       <td>{@link Measurement.NotApplicable}</td></tr>
 *   <tr><td>{@code unavailable} / not measured</td><td>empty</td>
 *       <td>{@link Measurement.NotMeasured}</td></tr>
 *   <tr><td>{@code unavailable} / not measured</td><td>non-empty</td>
 *       <td>{@link Measurement.FailedToMeasure}</td></tr>
 * </table>
 *
 * <p>So {@code not measured} with a weakening is not a not-measured with more explanation beside it.
 * It is the one way a document says a measurement was asked for, started, and could not be finished
 * — which is what {@code somethingWasUnreadable} was invented to get back, and what a reader of the
 * JSON could not get at all.
 *
 * <p><b>The value is not handed out.</b> This was a record, so it published an {@code Optional<T>}
 * accessor beside the word, and a renderer holding one could reach past the status to what it
 * wrapped exactly as the evidence records let it reach past the measurement — which is the shape
 * issue #997 was. What a caller can do with the value is ask for it under a guard ({@link #counted()}
 * then {@link #get()}) or be handed it only if there is one ({@link #ifMade}). Neither makes writing
 * a number for a measurement that has none impossible — {@code Measure.made()} is public and always
 * will be — and that is not what they are for. They make the serialization boundary have one door.
 */
final class ReportMeasurement<T> {

    private final MeasurementStatus status;
    private final MeasureReason reason;
    private final WeakeningSet weakenedBy;
    /** What the measure made, where it made anything. Absent is a measurement that was not made and
     *  never a zero standing in for one. */
    private final Optional<T> value;

    private ReportMeasurement(MeasurementStatus status, MeasureReason reason,
                              WeakeningSet weakenedBy, Optional<T> value) {
        this.status = status;
        this.reason = reason;
        this.weakenedBy = weakenedBy;
        this.value = value;
    }

    static <T> ReportMeasurement<T> of(Measure<T> measure) {
        return new ReportMeasurement<>(statusOf(measure), measure.why(),
                measure.weakening(), measure.made());
    }

    MeasurementStatus status() {
        return status;
    }

    MeasureReason reason() {
        return reason;
    }

    WeakeningSet weakenedBy() {
        return weakenedBy;
    }

    /** What the measure made, handed over only where it made anything. */
    void ifMade(java.util.function.Consumer<? super T> then) {
        value.ifPresent(then);
    }

    /**
     * The word for a level that has no measurement of its own — a behavior, a module, the report.
     *
     * <p>Such a level is complete exactly when nothing weakened it. It has no reason and no value:
     * there is no measure here that could fail to apply, only measures beneath it, and what they
     * went without is the whole of what this says.
     */
    static MeasurementStatus statusOf(WeakeningSet weakenedBy) {
        return weakenedBy.isEmpty() ? MeasurementStatus.COMPLETE : MeasurementStatus.PARTIAL;
    }

    private static MeasurementStatus statusOf(Measure<?> measure) {
        return switch (measure) {
            // The one word that is not about how far measuring got, and the only arm above
            // `Measurement` that produces it. A measure typed as a measurement cannot reach here.
            case Measure.NotApplicable<?> _ -> MeasurementStatus.NOT_APPLICABLE;
            case Measurement.Complete<?> _ -> MeasurementStatus.COMPLETE;
            case Measurement.Partial<?> _ -> MeasurementStatus.PARTIAL;
            case Measurement.NotMeasured<?> _ -> MeasurementStatus.NOT_MEASURED;
            // The fifth state, under the fourth word. What tells it from the one above is the
            // weakening this carries, which is why the two are emitted together and never apart.
            case Measurement.FailedToMeasure<?> _ -> MeasurementStatus.NOT_MEASURED;
        };
    }

    /** Whether this measure has a number to show. Where it has none, it has a reason instead. */
    boolean counted() {
        return value.isPresent();
    }

    /** Whether it was made and made in full, which is what a line that reads as settled needs. */
    boolean inFull() {
        return status == MeasurementStatus.COMPLETE;
    }

    /** The value, for a caller that has already asked {@link #counted()}. */
    T get() {
        return value.orElseThrow(() -> new IllegalStateException(
                "a measurement with no number was read for one: " + status));
    }
}
