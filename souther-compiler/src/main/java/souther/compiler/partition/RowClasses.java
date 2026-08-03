package souther.compiler.partition;

import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowOutcome;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Which class each of a row's inputs fell in.
 *
 * <p>A row writes values, not class names, so what it covers has to be read back out of what it was
 * given. The values are already the compiler's own ({@link ObservedValue}), so this is a walk down a
 * path and a question put to each class.
 *
 * <p>A value that could not be read leaves <em>that axis</em> unclassified and nothing else. A row
 * carrying one enormous string still says which case its other inputs were, and a measure that gave
 * up on the whole row because of an unrelated field would report gaps the row had already filled.
 */
public final class RowClasses {

    /** Where each axis's value fell, for the axes that have classes. An axis the model only bounds
     * has nothing to fall into and is left out. */
    public static Map<AxisId, Classification> of(RowOutcome row, List<String> parameters,
                                                 List<Axis> axes) {
        Map<AxisId, Classification> out = new LinkedHashMap<>();
        for (Axis axis : axes) {
            if (!axis.derivable()) {
                continue;
            }
            out.put(axis.id(), classify(row, parameters, axis));
        }
        return Map.copyOf(out);
    }

    /** The value this row put at {@code path}, or null where it did not put a readable one there.
     * What a boundary asks of a row: not which class it fell in, but whether it was the value. */
    public static ObservedValue valueAt(RowOutcome row, List<String> parameters, TermPath path) {
        int at = parameters.indexOf(path.head());
        if (at < 0 || at >= row.inputs().size()) {
            return null;
        }
        return walk(row.inputs().get(at), path.fields());
    }

    private static Classification classify(RowOutcome row, List<String> parameters, Axis axis) {
        int at = parameters.indexOf(axis.path().head());
        if (at < 0 || at >= row.inputs().size()) {
            return Classification.unreadable(Incompleteness.Code.VALUE_UNREADABLE,
                    axis.id().toString());
        }
        ObservedValue value = walk(row.inputs().get(at), axis.path().fields());
        if (value == null) {
            return Classification.unreadable(Incompleteness.Code.VALUE_UNREADABLE,
                    axis.id().toString());
        }
        if (value instanceof ObservedValue.Unknown) {
            return Classification.unreadable(Incompleteness.Code.VALUE_UNREADABLE,
                    axis.id().toString());
        }
        if (value instanceof ObservedValue.Truncated) {
            return Classification.unreadable(Incompleteness.Code.VALUE_TRUNCATED,
                    axis.id().toString());
        }
        for (PartitionClass each : axis.classes()) {
            if (each.classifier().matches(value)) {
                return Classification.in(each.id());
            }
        }
        // The classes are exhaustive over the position, so a value in none of them is one this could
        // not read rather than one outside the partition.
        return Classification.unreadable(Incompleteness.Code.VALUE_UNREADABLE, axis.id().toString());
    }

    /** The value at the end of a field chain, or null where the chain does not lead anywhere. A
     * newtype is never a step — the path never names its {@code value} — so what is walked here is
     * only a record's fields. */
    private static ObservedValue walk(ObservedValue from, List<String> fields) {
        ObservedValue at = from;
        for (String field : fields) {
            if (!(at instanceof ObservedValue.Constructed constructed)) {
                return null;
            }
            at = constructed.field(field);
            if (at == null) {
                return null;
            }
        }
        return at;
    }

    private RowClasses() {}
}
