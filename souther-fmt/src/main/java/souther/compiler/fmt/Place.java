package souther.compiler.fmt;

import souther.compiler.cst.SyntaxKind;

/**
 * One place of the canonical form: somewhere the formatter writes something, told apart from every
 * other place by being it.
 *
 * <p>Two siblings written as the same kind of construct are two places. An {@code if} written
 * {@code if flag then p else q} has three children that are all a {@code VAR_EXPR}, and its
 * condition, its then branch and its else branch are three places. Identity is the object's — a
 * place is not equal to another place that happens to look the same, because there is no other
 * place that is this one.
 *
 * <p>A place is not another name for a {@link souther.compiler.cst.SyntaxNode}. A definition
 * written {@code let f = (x) -> x} is written back as {@code let f (x) = x}, and the parameter list
 * there is a place the source tree has no node at. What the source had at a place is
 * {@link Correspondence}'s to say and not a field here: a place with one source element and a place
 * with none are both ordinary, and a field would make the first of those the only kind.
 *
 * <p>Which of its parent's places this is, is the label on the edge from the parent — the parent
 * and the ordinal together. Nothing else has to name it.
 */
final class Place {

    private final Place parent;
    private final int ordinal;
    private final SyntaxKind construct;
    private final Opening opening;

    Place(Place parent, int ordinal, SyntaxKind construct, Opening opening) {
        this.parent = parent;
        this.ordinal = ordinal;
        this.construct = construct;
        this.opening = opening;
    }

    /** The place this one is written inside, or null for the file. */
    Place parent() {
        return parent;
    }

    /** Which of its parent's places this is, counted in the order they are written. */
    int ordinal() {
        return ordinal;
    }

    /** What the canonical form writes here, named as it writes it rather than as the source had
     *  it. Null where what is written is a bare name rather than a construct. */
    SyntaxKind construct() {
        return construct;
    }

    Opening opening() {
        return opening;
    }

    @Override
    public String toString() {
        return (parent == null ? "file" : parent.construct() + "[" + ordinal + "]")
                + " " + construct;
    }
}
