package souther.compiler.observe;

/**
 * Why a measure has no number.
 *
 * <p>Which reasons a measure can have stays the measure's own business. What is not the measure's is
 * which kind of no-number a reason is, and that is now the reason's <em>type</em> rather than
 * something it answers: {@link NotApplicableReason}, {@link NotMeasuredReason} and
 * {@link FailureReason} are three interfaces and a constant implements exactly one.
 *
 * <p>It used to answer {@code status()} and {@code somethingWasUnreadable()}, and a measure whose
 * status and reason disagreed was refused where the value was built. A check over a state the type
 * still lets anybody write is a check somebody has to keep running; three types is the same rule
 * with nothing left to run (issue #953).
 *
 * <p>{@code name()} is here so that a document can write the constant's word without every reader
 * holding the enum. It is what {@link Enum} already provides, which is why every reason is one.
 */
public interface MeasureReason {

    /** The constant's own word, which is what the JSON form lowercases. */
    String name();
}
