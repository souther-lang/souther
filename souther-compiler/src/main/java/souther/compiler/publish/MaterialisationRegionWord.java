package souther.compiler.publish;

/**
 * What a document calls the way a build's region is named.
 *
 * <p>An enum for the reason {@link ThroughStepWord} is one.
 */
public enum MaterialisationRegionWord {

    /** A definition's body as a whole. */
    BODY,

    /** One of the regions a construct the source wrote opens. */
    SLOT,

    /** The body of a block the source wrote. */
    BLOCK,

    /** The body of a block a name written where a value goes was expanded into. */
    BLOCK_OF_NAME,

    /** One clause of a type's invariant as a whole. */
    INVARIANT,

    /** One arm of a behavior's ensures clause as a whole. */
    ENSURES
}
