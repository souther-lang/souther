package souther.compiler.fmt;

import souther.compiler.cst.SyntaxKind;

/**
 * The rule that the rows of a table write each of their connectors at one column, and the vocabulary
 * it is stated in.
 *
 * <p>A table is a construct whose rows are read against each other: which input differs between two
 * of them is what writing them one under the other is for. That is what an {@code example} and a
 * {@code fake} are and it is not what a {@code match} is — the arms of a match are read from the top
 * down, and a rule that lined their arrows up would move every arm to the width of the longest one
 * for no question anyone asks of them.
 *
 * <p><b>Not a second answer about a boundary.</b> {@link Spacing} decides what stands between two
 * tokens and still has no third answer. A stop is written <em>after</em> that answer, so what a
 * column says is where the connector after it begins and never what separates it from what came
 * before. A source whose table is already aligned and one that is not both hold one space there;
 * they differ in the padding, which is this rule's and nobody else's.
 *
 * <p><b>The stops are in the order a row writes them.</b> Where a column is depends on the ones
 * before it on the same line — a row's {@code ->} stands after however far its {@code :} pushed it —
 * so {@link Stop} is declared in that order and the layout settles them in it.
 */
final class Columns {

    private Columns() {
    }

    /**
     * Which table a column belongs to. An identity and nothing else, as {@link Doc.GroupRef} and
     * {@link Doc.NestRef} are: two {@code example}s written the same way are two tables, and a rule
     * keyed by what they are called would run the widths of one into the other.
     */
    static final class TableRef {
    }

    /** One column of one table. */
    record Unit(TableRef table, Stop stop) {

        Unit {
            if (table == null || stop == null) {
                throw new IllegalArgumentException("a column is one stop of one table");
            }
        }
    }

    /**
     * A place a table's rows line up at: the construct the row is, and the connector that stands at
     * the column.
     *
     * <p>Named by the connector rather than by how many stops come before it. A row with no
     * description has no {@code :} and its {@code ->} is still the same column as everybody else's;
     * counted by position it would be the first stop of that row and the second of the rest, and the
     * table would have two columns where it has one.
     */
    enum Stop {

        /** Where an example row's input begins. */
        THE_INPUT_OF_AN_EXAMPLE(SyntaxKind.EXAMPLE_ROW, SyntaxKind.COLON),

        /** Where an example row's expected value begins. */
        THE_RESULT_OF_AN_EXAMPLE(SyntaxKind.EXAMPLE_ROW, SyntaxKind.ARROW),

        /** Where a fake row's output begins. */
        THE_RESULT_OF_A_FAKE(SyntaxKind.FAKE_ROW, SyntaxKind.ARROW);

        private final SyntaxKind rowKind;
        private final SyntaxKind connector;

        Stop(SyntaxKind rowKind, SyntaxKind connector) {
            this.rowKind = rowKind;
            this.connector = connector;
        }

        /** What the row this is a stop of is written as. */
        SyntaxKind rowKind() {
            return rowKind;
        }

        /** The token written at the column. */
        SyntaxKind connector() {
            return connector;
        }

        /** What the rule says, for a reader who is being told their source does not. */
        String said() {
            return "the rows of a " + switch (rowKind) {
                case EXAMPLE_ROW -> "table of examples";
                case FAKE_ROW -> "table of fakes";
                default -> throw new IllegalStateException("no such table: " + rowKind);
            } + " write their " + connector.fixedSpelling().orElseThrow()
                    + " at one column";
        }
    }

    /**
     * Whether a construct's rows are read against each other. What holds a table's rows is what a
     * column's widths are closed over.
     */
    static boolean isTable(SyntaxKind kind) {
        return kind == SyntaxKind.EXAMPLE_DEF || kind == SyntaxKind.FAKE_DEF;
    }

    /**
     * The stop written at a boundary, or null where the boundary is not one.
     *
     * <p>Read from the construct joining the two tokens and the one on the right, which is the same
     * pair {@link Spacing} is asked about. The token on the left is not read: what a row writes
     * before its {@code ->} is its input, and an input is whatever the author put there.
     *
     * <p>{@code joining} is the deepest construct holding both tokens, so an arrow written inside
     * the row — a lambda's — is joined by that lambda and is not a stop of the table.
     */
    static Stop at(SyntaxKind joining, SyntaxKind right) {
        for (Stop stop : Stop.values()) {
            if (stop.rowKind() == joining && stop.connector() == right) {
                return stop;
            }
        }
        return null;
    }
}
