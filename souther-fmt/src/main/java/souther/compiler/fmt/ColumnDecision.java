package souther.compiler.fmt;

/**
 * Where one column of one table is, on the screen.
 *
 * <p>Taken once for the whole column, as a group's is taken once for the whole group. Which column
 * a table's {@code ->} stands at is one answer that every row of it is written to, so a decision per
 * row would be counting the rows and calling the count decisions.
 *
 * <p>A display column and not an index into the text. What lines up is what a reader sees, and the
 * rows of a table whose descriptions are Japanese line up where the columns agree and not where the
 * characters do.
 */
record ColumnDecision(Columns.Unit unit, int column) {
}
