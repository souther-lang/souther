package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;

/**
 * What names an axis across a report: the behavior it is an input of, and the number of that input
 * it measures — a location, or something taken of one.
 *
 * <p>A value rather than the axis itself, so that an obligation or a coverage row can say which axis
 * it is about without holding the classes and their classifiers.
 *
 * <p>The term as it prints, which is not always a location: {@code String.length(t.name)} is one of
 * these. Written out here because this crosses into a report, where an axis is a name and nothing
 * more — the structure it was made from is {@link NumericTerm} and stays inside the partition.
 */
public record AxisId(String behavior, String term) {

    public static AxisId of(String behavior, NumericTerm term) {
        return new AxisId(behavior, term.toString());
    }

    @Override
    public String toString() {
        return behavior + "/" + term;
    }
}
