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

    /**
     * Whether this is a measure that could not read what it needed, as against one nobody asked
     * for.
     *
     * <p>Both come back with no number and {@link MeasurementStatus#NOT_MEASURED} says so, which is
     * what a reader deciding whether to go and write a row wants. It is not what a reader deciding
     * how much of the run was made wants: a behavior nobody wrote a row for was measured exactly as
     * far as anybody asked, and one whose rules this compiler could not read was not. Told apart
     * only by the two words, the second was reported under a {@code measurement: complete} that the
     * measure beneath it contradicted.
     *
     * <p>The reason's own answer, for the reason {@link #status} is. Which reasons a measure can
     * have is that measure's business; that each of them knows which of these it is, is not, and a
     * reader working it out from the constant's name is a table that goes out of step with the
     * enum it copies.
     *
     * <p>False wherever there is a number, and false wherever nothing was there to read. It is
     * exactly {@code NOT_MEASURED} that divides — which is why this is here and not on
     * {@link MeasurementStatus}, where the two would have to be one word again.
     */
    boolean somethingWasUnreadable();
}
