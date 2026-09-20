package souther.compiler.publish;

/**
 * What a document calls which of the regions a construct opens a build was made for.
 *
 * <p>An enum for the reason {@link ThroughStepWord} is one.
 */
public enum RegionSlotWord {

    /** The arm an {@code if} takes when its condition holds. */
    IF_THEN,

    /** The arm an {@code if} takes when it does not. */
    IF_ELSE,

    /** The arm of an attempted construction that runs when the value was built. */
    CONSTRUCTED_THEN,

    /** The arm of an attempted construction that runs when it was refused. */
    CONSTRUCTED_ELSE,

    /** The arm of a {@code match} written for some cases. */
    MATCH_CASE,

    /** What stands on the right of {@code &&} or {@code ||}. */
    SHORT_CIRCUIT_RIGHT,

    /** The element a comprehension writes for each item. */
    COMPREHENSION_ELEMENT,

    /** One of a comprehension's guards. */
    COMPREHENSION_GUARD
}
