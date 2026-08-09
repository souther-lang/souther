package souther.compiler.fmt;

import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

/**
 * A source element a place was written from.
 *
 * <p>A node has an identity of its own, so it names itself. A name written as a run of identifiers
 * has none — a sum's cases are bare identifiers — so it is named by where it is, which is how the
 * formatter has always named one.
 */
sealed interface Written {

    Written[] NONE = new Written[0];

    /**
     * Where this element's own text ends.
     *
     * <p>Past whatever trivia the node carries after its last token, since that trivia is where a
     * comment written after it is. Asked of the element rather than worked out from the tree it is
     * in: how far a place reaches is a fact about what was written there.
     */
    int end();

    /** A construct of the source. Compared by identity, which is what the tree gives: one red node
     *  per position, handed back the same each time its parent is asked for its children. */
    record Construct(SyntaxNode node) implements Written {

        @Override
        public int end() {
            SyntaxToken last = lastCodeTokenOf(node);
            return last == null ? node.end() : last.end();
        }

        private static SyntaxToken lastCodeTokenOf(SyntaxNode n) {
            SyntaxToken last = null;
            for (SyntaxElement e : n.children()) {
                SyntaxToken found = e instanceof SyntaxNode c ? lastCodeTokenOf(c)
                        : e instanceof SyntaxToken t && !t.isTrivia() ? t : null;
                if (found != null) {
                    last = found;
                }
            }
            return last;
        }
    }

    /** A name the grammar wrote as identifiers, named by where it begins and ends. */
    record Run(int start, int end) implements Written {}

    static Written[] of(SyntaxNode node) {
        return node == null ? NONE : new Written[] {new Construct(node)};
    }
}
