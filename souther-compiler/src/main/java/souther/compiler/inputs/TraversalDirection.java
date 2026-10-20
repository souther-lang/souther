package souther.compiler.inputs;

/**
 * The end of a list a walk over its elements starts at: the first the row writes, or the last.
 *
 * <p>Two values, and not a permutation. What is known of an operation that puts a list's elements
 * in another order is that it turns the order round or says nothing, and turning round twice is
 * the order written, so the one operation that does it composes with itself by {@link #reversed}.
 */
public enum TraversalDirection {

    /** The first element the row writes is handed first. */
    FORWARD,

    /** The last element the row writes is handed first. */
    REVERSE;

    /** The direction of a walk over the same elements handed the other way round. */
    public TraversalDirection reversed() {
        return this == FORWARD ? REVERSE : FORWARD;
    }
}
