package souther.compiler.partition;

/**
 * One line a fill composed, and what looking for a line that goes further came to.
 *
 * <p>One value under the row's number, so that whatever copies or renumbers the line copies the
 * account with it. Held as a second table beside the lines, the account would be one more thing
 * every renumbering has to know to carry, and the one that forgot would hand a reader a row
 * stopping at a guard with nothing said about it.
 *
 * <p>The line is still only the line. What the looking came to is no part of what the line is
 * written as, so two of these with one line are one line in the file however the looking went.
 *
 * @param line   the line
 * @param repair what looking for a row that goes further came to, or null where there is nothing
 *               to say about a guard: the row was not stopped at one, or nothing says how far it
 *               got, or it is a row nothing looks past a guard for
 */
public record FilledRow(ComposedRow line, RepairShortfall repair) {

    public FilledRow {
        if (line == null) {
            throw new IllegalArgumentException("a filled row is a line");
        }
    }
}
