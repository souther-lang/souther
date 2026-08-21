package souther.compiler.flow;

/**
 * The path of a reading that names nothing.
 *
 * <p>A value rather than an absence. What a reading with no numbering behind it knows about the way
 * to a value is that there was one, and that is a thing to say and not a thing missing — written as
 * null it would put a hole in every path this reading answers with and make "no conditions" and "no
 * path" the same shape.
 */
public enum AnonymousPath {

    /** The one path such a reading has words for. */
    INSTANCE;

    @Override
    public String toString() {
        return "(unnamed)";
    }
}
