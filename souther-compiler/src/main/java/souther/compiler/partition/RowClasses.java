package souther.compiler.partition;

import souther.compiler.inputs.Membership;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowOutcome;

import java.util.ArrayList;
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
    public static Map<AxisId, Classification> of(RowOutcome row, BehaviorInputs where,
                                                 List<Axis> axes) {
        Map<AxisId, Classification> out = new LinkedHashMap<>();
        for (Axis axis : axes) {
            if (!axis.derivable()) {
                continue;
            }
            out.put(axis.id(), classify(row, where, axis));
        }
        return Map.copyOf(out);
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
    private static Classification classify(RowOutcome row, BehaviorInputs where, Axis axis) {
        List<ObservedValue> values = where.valuesAt(row, axis.path());
        if (values == null) {
            return Classification.unreadable(Incompleteness.Code.VALUE_UNREADABLE,
                    axis.id().behavior(), axis.id().term());
        }
        // Every value the row put here, and every class any of them is in. One at most positions;
        // as many as the row wrote at a position inside a sequence, where they need not fall
        // together — and where one of them being unreadable leaves the classes the others reached
        // standing, since each is a value of its own.
        List<String> in = new ArrayList<>();
        Incompleteness.Code stopped = null;
        for (ObservedValue value : values) {
            Classification each = classifyOne(row, where, axis, value);
            switch (each) {
                case Classification.Classified found -> found.classIds().forEach(id -> {
                    if (!in.contains(id)) {
                        in.add(id);
                    }
                });
                case Classification.Unclassified why -> {
                    if (stopped == null) {
                        stopped = why.reason().code();
                    }
                }
            }
        }
        if (!in.isEmpty()) {
            return Classification.in(in);
        }
        if (stopped != null) {
            return Classification.unreadable(stopped, axis.id().behavior(), axis.id().term());
        }
        // Read, and in no class. A row whose list holds no element is one: there was nothing at
        // this position to be in a class, which is not a reading that stopped.
        return values.isEmpty() ? Classification.in(List.of())
                : classifyOne(row, where, axis, values.get(0));
    }

    /** Where one value at the position falls, or why no class could say. */
    private static Classification classifyOne(RowOutcome row, BehaviorInputs where, Axis axis,
                                              ObservedValue value) {
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

    private RowClasses() {}
}
