package souther.compiler.flow;

/**
 * What one path arrives with.
 *
 * <p>Three answers and not two truths and a set. A path that arrives is a path whichever value it
 * came to, and {@link #UNREAD} says this reading has no answer for which of the two it was — it does
 * not say the path is missing and it does not say both are reachable. There is no way to spell "both"
 * here on purpose: a value that comes out both ways is two paths, and a reading that could summarise
 * it as one answer would be a place for "either, I cannot tell" and "each of them, I have seen a way"
 * to be written the same.
 *
 * <p>So {@link #TRUE} and {@link #FALSE} are only ever put on a path this reading worked out a value
 * for. Nothing widens {@link #UNREAD} into them and nothing reads a missing path as one of them.
 */
public enum Truth {

    /** This path arrives with true. */
    TRUE,

    /** This path arrives with false. */
    FALSE,

    /** This path arrives with a value, and which value is not something this reading says. */
    UNREAD;

    /** The truth of a value written out. */
    public static Truth of(boolean value) {
        return value ? TRUE : FALSE;
    }
}
