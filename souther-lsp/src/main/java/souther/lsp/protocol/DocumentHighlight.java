package souther.lsp.protocol;

/**
 * One place in the document being read that means the same thing as the place the cursor is on.
 *
 * <p>{@code kind} says which end of that it is. The protocol has three and this server uses two: a
 * declaration binds the name and a use reads it, which is a difference an editor paints — the third,
 * {@link #TEXT}, is what a highlight made by matching characters says about itself, and none of
 * these are made that way.
 */
public record DocumentHighlight(Range range, int kind) {

    /** A match nothing resolved: characters that look the same. Not answered here. */
    public static final int TEXT = 1;

    /** The name is read here. */
    public static final int READ = 2;

    /** The name is bound here. */
    public static final int WRITE = 3;
}
