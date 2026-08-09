package souther.compiler.fmt;

import souther.compiler.cst.SyntaxNode;

/**
 * A source element a place was written from.
 *
 * <p>A node has an identity of its own, so it names itself. A name written as a run of identifiers
 * has none — a sum's cases are bare identifiers — so it is named by where it is, which is how the
 * formatter has always named one.
 */
sealed interface Written {

    Written[] NONE = new Written[0];

    /** A construct of the source. Compared by identity, which is what the tree gives: one red node
     *  per position, handed back the same each time its parent is asked for its children. */
    record Construct(SyntaxNode node) implements Written {}

    /** A name the grammar wrote as identifiers, named by where it begins and ends. */
    record Run(int start, int end) implements Written {}

    static Written[] of(SyntaxNode node) {
        return node == null ? NONE : new Written[] {new Construct(node)};
    }
}
