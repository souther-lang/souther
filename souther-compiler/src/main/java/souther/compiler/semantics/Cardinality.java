package souther.compiler.semantics;

/**
 * How the size of a construction's result relates to the size of the container it was built from.
 *
 * <ul>
 * <li>{@code SAME} — exactly as many. Not stated as a fact of its own: both are one number, since
 *     the size of the result is answered with the size of its source.
 * <li>{@code AT_MOST} — no more, and possibly fewer.
 * </ul>
 */
public enum Cardinality {
    SAME, AT_MOST
}
