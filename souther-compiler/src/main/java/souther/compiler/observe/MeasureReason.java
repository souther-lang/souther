package souther.compiler.observe;

/**
 * Why a measure has no number, and which of the two kinds of no-number that is.
 *
 * <p>Which reasons a measure can have stays the measure's own business — this says only that a
 * reason knows whether it is one nothing can be done about or one that says what to do. Kept on the
 * reason rather than chosen beside it, so that a measure cannot come back saying its arms do not
 * apply and that somebody should go and measure them.
 */
public interface MeasureReason {

    /** {@link MeasurementStatus#NOT_APPLICABLE} or {@link MeasurementStatus#NOT_MEASURED}. */
    MeasurementStatus status();
}
