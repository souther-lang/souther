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

    /**
     * Which class the row's value at {@code axis} fell in, or why none of them could say.
     *
     * <p>The classes answer for themselves, including about a value none of them could read. This
     * used to test the value's shape here first, which is the same question asked in a second place
     * and answered from a different node: a classifier may read through the value — a number at a
     * position is the number inside the newtype named there — so a limit reached one level in left
     * a construction this saw nothing wrong with, and the reason came out as the one the last line
     * had to guess.
     */
    private static Classification classify(RowOutcome row, List<String> parameters, Axis axis) {
        int at = parameters.indexOf(axis.path().head());
        if (at < 0 || at >= row.inputs().size()) {
            return Classification.unreadable(Incompleteness.Code.VALUE_UNREADABLE,
                    axis.id().behavior(), axis.id().term());
        }
        ObservedValue value = walk(row.inputs().get(at), axis.path().fields());
        // Kept rather than returned on, and not acted on either. A class may read less of a value
        // than the one after it, so one saying it could not read says nothing about the rest —
        // including that the rest cannot hold it. An incompleteness is what is left once no class
        // has claimed the value, so nothing about it is decided until every class has answered.
        Incompleteness.Code incomplete = null;
        boolean disagreed = false;
        for (PartitionClass each : axis.classes()) {
            switch (each.classifier().membershipOf(value)) {
                case Membership.Match _ -> {
                    return Classification.in(each.id());
                }
                case Membership.Incomplete why -> {
                    if (incomplete == null) {
                        incomplete = why.code();
                    } else if (incomplete != why.code()) {
                        disagreed = true;
                    }
                }
                case Membership.NoMatch _ -> { }
            }
        }
        // Two readings of one value that disagree about whether it is there. Held to rather than
        // picked between: today every class of a numeric position reads through the same reader,
        // so nothing produces one.
        if (disagreed) {
            throw new IllegalStateException("classes of " + axis.id()
                    + " disagree about why the value could not be read");
        }
        if (incomplete != null) {
            return Classification.unreadable(incomplete,
                    axis.id().behavior(), axis.id().term());
        }
        // Every class read the value and none holds it, which `Axis` says cannot happen: its classes
        // are exhaustive over the position's values. So this is that contract broken rather than
        // anything about the row, and saying the value could not be read would be reporting a
        // measurement failure for a defect in the partition.
        throw new IllegalStateException("no class of " + axis.id() + " holds a value it read: "
                + value);
    }

    /**
     * The value at the end of a field chain, or null where the chain does not lead anywhere. A
     * newtype is never a step — the path never names its {@code value} — so what is walked here is
     * only a record's fields.
     *
     * <p>An observation that stopped is handed on rather than walked into. It is not a record and
     * there is nothing under it, but it is also not a chain that leads nowhere: it is the reason
     * this position has no value, and it says that itself. Read as somewhere the walk could not go,
     * a limit that ran out one field short of a position came back as a value nobody could read —
     * the same observation the walk returns as it stands when the path happens to end on it.
     *
     * <p>Which leaves null for the walk's own answer, and only that: a record that does not hold the
     * field named next, or a value that was read and is not a record at all. The path and the shape
     * disagree, and no observation says why because nothing went wrong with one.
     */
    private static ObservedValue walk(ObservedValue from, List<String> fields) {
        ObservedValue at = from;
        for (String field : fields) {
            if (at.unread() != null) {
                return at;
            }
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
