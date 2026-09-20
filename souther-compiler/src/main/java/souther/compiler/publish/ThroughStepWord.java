package souther.compiler.publish;

/**
 * What a document calls one step a copy of a construct was made by.
 *
 * <p>An enum so that the words the shipped schema names for {@code through} are held against
 * something: a word added here has to be taught to the schema before it can be written.
 */
public enum ThroughStepWord {

    /** A call the copy was made at. */
    EXPANSION,

    /** One build of a value's body, for the region it names. */
    MATERIALISATION
}
