package souther.compiler.observe;

/**
 * Why a measurement that was started could not be finished.
 *
 * <p>The state that had no word. A measure whose rules this compiler could not read and one nobody
 * wrote a row for were both {@code NOT_MEASURED}, and the difference — which of them leaves every
 * number around it weaker than it looks — was recovered by asking the reason a boolean
 * ({@code somethingWasUnreadable}). A reader who did not know to ask got the wrong one.
 *
 * <p>A measurement that failed carries what it went without beside this, the way a partial one does.
 * The reason says what kind of nothing came back; the weakening says what would have been needed.
 */
public interface FailureReason extends MeasureReason {}
