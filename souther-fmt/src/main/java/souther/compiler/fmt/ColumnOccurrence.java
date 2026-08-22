package souther.compiler.fmt;

/**
 * One row written to a column: where that row would have reached on its own, and where in the text
 * the padding that carries it to the column stands.
 *
 * <p>The occurrences are to a {@link ColumnDecision} what the opportunities are to a group's: the
 * decision is one and the places it is realized at are many. What makes the pair worth keeping is
 * that the decision cannot be read back off the text — every row of a table is at the column, so a
 * text says where the column is and never which row put it there.
 *
 * <p>{@code naturalColumn} is where the connector stands with every column before it on this line
 * already written and this one not — so the column is the greatest of them, and a row whose natural
 * column is the column is one the rule writes nothing for.
 *
 * <p>Only for a row the canonical form writes on one line. A row it breaks has its connector at the
 * start of a line, where a column is not a thing that could be asked about.
 */
record ColumnOccurrence(Columns.Unit unit, int at, int naturalColumn) {
}
