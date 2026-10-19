package souther.compiler.inputs;

/**
 * Which of the occurrences of a run are counted: the ones meeting a statement, as a list a filter
 * kept some of holds them.
 *
 * <p>Only the identity is here. What the statement says and how a row is put to it belong where
 * statements are, and a number of the input does not know them; two selections are the same where
 * they say the same, which is what {@link #key} is.
 */
public interface OccurrenceSelection {

    /** What this selects, spelled so that two selections saying the same spell it alike. */
    String key();
}
