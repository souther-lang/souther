package souther.compiler.cst.contract;

import java.util.ArrayList;
import java.util.List;

/**
 * A node of the contract syntax tree: the tree the grammar says a source is, named by the
 * grammar's {@code @node} productions and holding nothing an implementation chooses.
 *
 * <p>Written and read as the S-expression tree-sitter's corpus format uses — {@code (id child ...)}
 * — so the corpus under {@code syntax/corpus} is one an external implementation can run as it is.
 */
record ContractTree(String id, List<ContractTree> children) {

    ContractTree {
        children = List.copyOf(children);
    }

    static ContractTree leaf(String id) {
        return new ContractTree(id, List.of());
    }

    /** The identifier of this node and of every node under it. */
    void collectIds(List<String> into) {
        into.add(id);
        for (ContractTree child : children) {
            child.collectIds(into);
        }
    }

    @Override
    public String toString() {
        StringBuilder out = new StringBuilder();
        write(out, 0);
        return out.toString();
    }

    /** One node per line, each child two spaces in from its parent, as the corpus is written. */
    private void write(StringBuilder out, int depth) {
        out.append("  ".repeat(depth)).append('(').append(id);
        if (children.isEmpty()) {
            out.append(')');
            return;
        }
        for (ContractTree child : children) {
            out.append('\n');
            child.write(out, depth + 1);
        }
        out.append(')');
    }

    /**
     * The tree an S-expression writes. Whitespace between parentheses is not read, so the corpus
     * may lay a tree out however reads best.
     */
    static ContractTree parse(String written) {
        Reader reader = new Reader(written);
        ContractTree tree = reader.tree();
        reader.skipSpace();
        if (reader.pos != written.length()) {
            throw new IllegalArgumentException("text after the tree at " + reader.pos + ": " + written);
        }
        return tree;
    }

    private static final class Reader {
        private final String text;
        private int pos;

        Reader(String text) {
            this.text = text;
        }

        ContractTree tree() {
            skipSpace();
            expect('(');
            int start = pos;
            while (pos < text.length() && !Character.isWhitespace(text.charAt(pos))
                    && text.charAt(pos) != '(' && text.charAt(pos) != ')') {
                pos++;
            }
            String id = text.substring(start, pos);
            if (id.isEmpty()) {
                throw new IllegalArgumentException("a node with no name at " + start + ": " + text);
            }
            List<ContractTree> children = new ArrayList<>();
            skipSpace();
            while (pos < text.length() && text.charAt(pos) == '(') {
                children.add(tree());
                skipSpace();
            }
            expect(')');
            return new ContractTree(id, children);
        }

        void skipSpace() {
            while (pos < text.length() && Character.isWhitespace(text.charAt(pos))) {
                pos++;
            }
        }

        private void expect(char c) {
            if (pos >= text.length() || text.charAt(pos) != c) {
                throw new IllegalArgumentException("expected `" + c + "` at " + pos + ": " + text);
            }
            pos++;
        }
    }
}
