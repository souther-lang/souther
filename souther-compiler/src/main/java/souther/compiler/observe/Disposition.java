package souther.compiler.observe;

/**
 * How an {@code example} row ended.
 *
 * <p>{@link #INCOMPLETE} is not a failure. A row that ran out of time or found no runtime to run
 * against says nothing about the model — reporting it as a failing example would put a diagnostic on
 * something that may well be right, and counting it as covering nothing would report a gap nobody
 * left. It is an absence of evidence, and the measures that read it treat it as one.
 */
public enum Disposition {

    /** The row is recorded but not evaluated: its target has no {@code let} body yet. */
    PENDING,

    /** The row ran and its expectation held. */
    HELD,

    /** The row ran, or tried to, and the model did not do what the row says. */
    FAILED,

    /** Nothing was decided — the evaluation could not finish. */
    INCOMPLETE
}
