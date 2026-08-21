package souther.compiler.partition;

import souther.compiler.check.Shape;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.StructuralDescent;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowOutcome;
import souther.compiler.types.Type;

import java.util.ArrayList;
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
public record BehaviorInputs(List<String> parameters, List<Type> types, Symbols symbols,
                             souther.compiler.check.ReadingPolicy policy) {

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
     * The values this row put at {@code path}, which is one value at most positions and however
     * many the row wrote at a position inside a sequence.
     *
     * <p>Empty where it put no readable one there, and never null: a caller asking what a row
     * covers at a position is answered with what it wrote, and a list of none is a row that wrote
     * none — which a row holding an empty list did.
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
     * <p>Which leaves nothing for the walk's own answer, and only that: a record that does not hold
     * the field named next, or a position whose type is not a record at all. The path and the type
     * disagree, and no observation says why because nothing went wrong with one.
     */
    public List<ObservedValue> valuesAt(RowOutcome row, TermPath path) {
        int at = indexOf(path);
        if (at < 0 || at >= row.inputs().size()) {
            return null;
        }
        List<Standing> standing = List.of(new Standing(row.inputs().get(at), types.get(at)));
        boolean[] broke = {false};
        for (TermPath.Step step : path.steps()) {
            List<Standing> next = new ArrayList<>();
            for (Standing each : standing) {
                if (!each.step(step, symbols, next)) {
                    broke[0] = true;
                }
            }
            standing = next;
        }
        // Nothing here, and two ways for that to be so. A step that could not be taken is the walk
        // and the type disagreeing, which is what null has always said; a sequence holding no
        // element is a row that wrote none, which is a reading that arrived. Answered alike, a row
        // writing the empty list would be reported as one nothing could be read from.
        if (standing.isEmpty() && broke[0]) {
            return null;
        }
        return standing.stream().map(Standing::value).toList();
    }

    /**
     * The value this row put at {@code path}, or null where it did not put one readable value
     * there.
     *
     * <p>For a position one value stands at. A position inside a sequence has as many as the row
     * wrote, and answering a caller that wants one with the first of them would report what a row
     * covers off an element it chose — so such a position answers null here and {@link #valuesAt}
     * is what reads it.
     */
    public ObservedValue valueAt(RowOutcome row, TermPath path) {
        List<ObservedValue> values = valuesAt(row, path);
        return values != null && values.size() == 1 ? values.get(0) : null;
    }

    /**
     * One value on the way down a path, with the type the declaration puts there.
     *
     * <p>A list of these and not one, because a step into what a sequence holds turns one value
     * into as many as it holds. Everything else keeps the count it had.
     */
    private record Standing(ObservedValue value, Type type) {

        /** Takes {@code step}, adding what stands below. False where it could not be taken. */
        boolean step(TermPath.Step step, Symbols symbols, List<Standing> out) {
            if (value.unread() != null) {
                out.add(this);
                return true;
            }
            TypeView view = TypeView.of(type, symbols);
            ObservedValue here = Classifier.inside(
                    view.wrappers().stream().map(TypeOps.Layer::named).toList(), value);
            if (here.unread() != null) {
                out.add(new Standing(here, type));
                return true;
            }
            switch (step) {
                case TermPath.Step.Field named -> {
                    StructuralDescent.Children children = StructuralDescent.of(view.shape());
                    if (children == null || !(here instanceof ObservedValue.Constructed made)) {
                        return false;
                    }
                    Type next = children.under().get(named.name());
                    ObservedValue held = made.field(named.name());
                    if (next == null || held == null) {
                        return false;
                    }
                    out.add(new Standing(held, next));
                }
                // Every element the row wrote, and no choice among them. Which of them a rule is
                // about is not something the coordinate says, so what stands here is all of them
                // and what a class comes to over them is the caller's to decide. A list holding
                // none is a step taken: the walk arrived and the row wrote nothing there.
                case TermPath.Step.Element _ -> {
                    if (!(view.shape() instanceof Shape.Sequence sequence)
                            || !(here instanceof ObservedValue.Sequence written)) {
                        return false;
                    }
                    written.elements().forEach(
                            element -> out.add(new Standing(element, sequence.element())));
                }
            }
            return true;
        }
    }
}
