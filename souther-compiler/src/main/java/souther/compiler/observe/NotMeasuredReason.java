package souther.compiler.observe;

/**
 * Why a measure that could have been made was not.
 *
 * <p>Says what to do: write a row, ask for the arms. Nothing went wrong — the measurement was never
 * started, so there is nothing it went without and nothing here weakens a measure above it.
 *
 * <p>That last part is what separates this from {@link FailureReason}. A measurement nobody asked
 * for and one that was asked for and could not read what it needed both come back with no number,
 * and only the second means the numbers around it are worth less than they look.
 */
public interface NotMeasuredReason extends MeasureReason {}
