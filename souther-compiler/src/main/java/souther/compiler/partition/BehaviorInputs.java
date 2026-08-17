package souther.compiler.partition;

import souther.compiler.check.Shape;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowOutcome;
import souther.compiler.types.Type;

import java.util.List;

/**
 * What a behavior takes: what its inputs are called, what they are declared to be, and what those
 * names denote.
 *
 * <p>One value because reading a row at a position needs all three. A path names a parameter and
 * the fields under it, a row's values arrive in the order the parameters are declared, and how a
 * value at a position is written — the names it wears — is what the declared types say. Given only
 * the first two, a reader walks a row by taking fields off values, which is right until a field
 * sits under a name.
 *
 * <p>And because the same three are what a row is generated from. Two spellings of what a behavior
 * takes are two chances to read a position differently, which is the shape of every defect this
 * package has been fixing: {@link Generator.Subject} is these inputs and the axes derived at them.
 */
public record BehaviorInputs(List<String> parameters, List<Type> types, Symbols symbols) {

    public BehaviorInputs {
        parameters = List.copyOf(parameters);
        types = List.copyOf(types);
    }

    /** Which input {@code path} starts at, or -1 where the behavior has no such parameter. */
    int indexOf(TermPath path) {
        int at = parameters.indexOf(path.head());
        return at < types.size() ? at : -1;
    }

    /**
     * The value this row put at {@code path}, or null where it did not put a readable one there.
     *
     * <p>The one walk into a row's values, done with the declared types beside them. A field of a
     * record is reached through the names the record is written under: {@code data SlotN = Slot} is
     * one position whose fields a partition is derived at, and a row writes
     * {@code SlotN(Slot { flag = true })}. The path never spells those names — a newtype is not a
     * step — so what reads the path takes them off. Walked on the values alone, the derivation
     * reached a field that the reading of a row could not, and every row at such a position came
     * back unreadable.
     *
     * <p><b>On the way and not at the end.</b> What comes back is the value as the position wears
     * it, names and all. Which names the position itself is written under is what tells a class
     * from another there ({@link Classifier#under}), so a walk that went on peeling would answer a
     * classifier with a value it no longer recognises — and the reading of what a position is would
     * have lost how it is written, one layer down from where this branch put it back.
     *
     * <p>An observation that stopped is handed on rather than walked into. It is not a record and
     * there is nothing under it, but it is also not a chain that leads nowhere: it is the reason
     * this position has no value, and it says that itself.
     *
     * <p>Which leaves null for the walk's own answer, and only that: a record that does not hold
     * the field named next, or a position whose type is not a record at all. The path and the type
     * disagree, and no observation says why because nothing went wrong with one.
     */
    public ObservedValue valueAt(RowOutcome row, TermPath path) {
        int at = indexOf(path);
        if (at < 0 || at >= row.inputs().size()) {
            return null;
        }
        ObservedValue value = row.inputs().get(at);
        Type here = types.get(at);
        for (String field : path.fields()) {
            if (value.unread() != null) {
                return value;
            }
            TypeView view = TypeView.of(here, symbols);
            value = Classifier.inside(
                    view.wrappers().stream().map(TypeOps.Layer::named).toList(), value);
            if (value.unread() != null) {
                return value;
            }
            if (!(view.shape() instanceof Shape.Product product)
                    || !(value instanceof ObservedValue.Constructed constructed)) {
                return null;
            }
            Type next = product.fields().get(field);
            ObservedValue held = constructed.field(field);
            if (next == null || held == null) {
                return null;
            }
            value = held;
            here = next;
        }
        return value;
    }
}
