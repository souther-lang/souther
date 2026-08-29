package souther.compiler.partition;

import java.util.List;

/**
 * One row's worth of input, and nothing about what it was composed for.
 *
 * <p>What it answers is the discharge's to say. Held here as well, the two were free to disagree:
 * a row composed for a class and later found to take an arm was merged into one line, the merged
 * line replaced the row a reader is offered, and the class's own entry went on holding the line
 * from before the merge. Nobody read the stale one, and the next reader would have.
 *
 * @param inputs one value per parameter, in the order the behavior takes them
 */
public record ComposedRow(List<FixtureTemplate> inputs) {

    public ComposedRow {
        inputs = List.copyOf(inputs);
    }

    /** What the row is written as, which is what tells one line of a file from another. */
    public List<String> writtenAs() {
        return inputs.stream().map(FixtureTemplate::text).toList();
    }
}
