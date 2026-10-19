package souther.compiler.inputs;

/**
 * Which of the occurrences of a run are counted: the ones meeting a statement, as a list a filter
 * kept some of holds them.
 *
 * <p>Only the identity is here. What the statement says and how a row is put to it belong where
 * statements are, and a number of the input does not know them. Two selections are the same where
 * their {@code equals} says so, which is what two numbers of the input counting under them are
 * told apart by; {@link #key} spells one for a reader and for a coordinate, and is no identity.
 */
public interface OccurrenceSelection {

    /** What this selects, spelled for a reader. */
    String key();
}
