package souther.compiler.partition;

import souther.compiler.check.Shape;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.Refinement;
import souther.compiler.check.StructuralDescent;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

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
     * The values written at {@code path}, which is one value at most positions and however many
     * were written at a position inside a sequence.
     *
     * <p>Empty where none readable is there, and never null: a caller asking what is covered at a
     * position is answered with what was written, and a list of none is nothing written there —
     * which an empty list is.
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
    public List<ObservedValue> valuesAt(List<ObservedValue> inputs, TermPath path) {
        List<Occurrence> found = occurrencesAt(inputs, path);
        return found == null ? null : found.stream().map(Occurrence::value).toList();
    }

    /**
     * One value a row put at {@code path}, and which element was taken to reach it at each step
     * inside a sequence.
     *
     * <p>The element and not only the value, because a relation between two positions is about one
     * element and not about the two sets. A row holding one person under a line and another over it
     * has values on both sides at {@code people[*].age} and values in both classes at
     * {@code people[*].status}, and which went with which is the whole of what a pair says — read
     * off the sets, the pairs one row covers are every combination of them, and a row is counted as
     * evidence for a combination none of its elements is in.
     *
     * @param at which element was taken, by the step it was taken at — the path up to and
     *           including that step inside a sequence. Empty where the path enters no sequence,
     *           which is one occurrence and stands with every other
     */
    public record Occurrence(Map<TermPath, Integer> at, ObservedValue value) {

        public Occurrence {
            at = Map.copyOf(at);
        }

        /**
         * Whether this and {@code other} can be one reading of the row.
         *
         * <p>Every step the two took together was taken at the same element, and the steps they did
         * not take together are free. Keyed by the step rather than counted, so the rule is one
         * sentence and every case follows from it: two positions under one person agree about the
         * person; a zip code and a phone number under one person agree about the person and not
         * about the address or the phone; two positions under different parameters share nothing
         * and stand with each other however they are spelled; and a position inside no sequence
         * takes no step, so it stands with everything.
         *
         * <p>Counted instead — the first so many elements of one list against the first so many of
         * another — two sibling collections would be zipped, which is a relation neither the row
         * nor the model states.
         */
        public boolean agreesWith(Occurrence other) {
            for (Map.Entry<TermPath, Integer> each : at.entrySet()) {
                Integer beside = other.at().get(each.getKey());
                if (beside != null && !beside.equals(each.getValue())) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * The values at {@code path}, each with the elements taken to reach it.
     *
     * <p>Asked of the values and not of a row. What falls where is a question about a tuple of
     * values, and rows are not the only things that have one: a value a {@code let} binds and a
     * candidate this package composed are both read at these positions, and both have to be read
     * the way a written row is or the classes they land in are two readings rather than one.
     */
    public List<Occurrence> occurrencesAt(List<ObservedValue> inputs, TermPath path) {
        int at = indexOf(path);
        if (at < 0 || at >= inputs.size()) {
            return null;
        }
        List<Standing> standing = List.of(new Standing(inputs.get(at), types.get(at),
                TermPath.of(path.head()), Map.of()));
        for (TermPath.Step step : path.steps()) {
            List<Standing> next = new ArrayList<>();
            int took = 0;
            for (Standing each : standing) {
                if (each.step(step, symbols, next)) {
                    took++;
                }
            }
            // A step is taken by everything standing here or the reading stops. What decides it is
            // the shape of a value against the type declared for it, and everything standing at one
            // position of one row was written under one declaration -- so this is all or none, and
            // a value nothing could read is carried down as one rather than failing the step. Kept
            // as one flag for the whole walk, what survived was answered with and whatever could
            // not be reached was left out with nothing saying so.
            if (took != standing.size()) {
                return null;
            }
            standing = next;
        }
        // Nothing here is a row that wrote no element, which is a reading that arrived: a step that
        // could not be taken has already answered null above. Answered alike, a row writing the
        // empty list would be reported as one nothing could be read from.
        return standing.stream().map(each -> new Occurrence(each.at(), each.value())).toList();
    }

    /**
     * What the declarations put at {@code path}, or null where they put nothing there.
     *
     * <p>The same walk {@link #occurrencesAt} takes, with the values left out. A position's type is
     * a fact about the declarations and a row is not needed to ask it — which is what a caller
     * composing a value at a position wants, since there is no row yet.
     *
     * <p><b>Here because the walk is here.</b> How a step of a path moves the type is one rule with
     * several cases — a field is reached through the names its record is written under, an element
     * is what a sequence holds, a refinement is the position read as one of its cases — and written
     * a second time for a caller that only wanted the type, the two would agree until one of them
     * learned a step the other did not.
     *
     * <p>Null where the path and the declarations disagree, and null for a path this behavior has no
     * parameter for. Neither is a position with a type nothing could name: they are paths that name
     * no position of these inputs at all.
     */
    public Type declaredAt(TermPath path) {
        int at = indexOf(path);
        if (at < 0) {
            return null;
        }
        Type here = types.get(at);
        for (TermPath.Step step : path.steps()) {
            here = stepping(step, here, symbols);
            if (here == null) {
                return null;
            }
        }
        return here;
    }

    /**
     * The type one step reaches from {@code from}, or null where the step is not one this position
     * takes.
     *
     * <p>Exhaustive over {@link TermPath.Step}, with no {@code default}, and the one place a step is
     * turned into a type. A step added later stops this compiling rather than arriving as a walk
     * that quietly takes it one way here and another way where a row is read.
     */
    static Type stepping(TermPath.Step step, Type from, Symbols symbols) {
        TypeView view = TypeView.of(from, symbols);
        return switch (step) {
            case TermPath.Step.Field named -> {
                // Null at a sum whose cases share a spread, where a field of the shared part does
                // stand at every value here. {@link StructuralDescent} is asked both what can be
                // read at a shape and what a value there is built out of, and a sum is the one
                // shape where those part company — it is read as the common product and built as
                // one of its cases. Reading it here would be a third place that knows the
                // difference, and the two questions have not been separated yet.
                StructuralDescent.Children children = StructuralDescent.of(view.shape());
                yield children == null ? null : children.under().get(named.name());
            }
            case TermPath.Step.Element _ -> view.shape() instanceof Shape.Sequence sequence
                    ? sequence.element() : null;
            // What a sum's case holds is the value the sum held, and what an optional holds is at
            // no name of its own — so both narrow the type at this position and nothing is
            // descended into.
            case TermPath.Step.Refine refine -> switch (refine.refinement()) {
                case Refinement.SumCase one -> view.shape() instanceof Shape.Sum
                        ? Type.ref(one.leaf()) : null;
                case Refinement.Presence presence ->
                        !(view.shape() instanceof Shape.Optional optional) ? null
                                : presence.present() ? optional.element() : view.declared();
            };
        };
    }

    /**
     * The value at {@code path}, or null where there is not one readable value there.
     *
     * <p>For a position one value stands at. A position inside a sequence has as many as were
     * written, and answering a caller that wants one with the first of them would report what is
     * covered off an element it chose — so such a position answers null here and {@link #valuesAt}
     * is what reads it.
     *
     * <p><b>Null runs three answers together, and a caller that has to tell them apart asks
     * {@link #occurrencesAt}.</b> The walk could not be taken, or it was taken and the row stands
     * nowhere here — the empty list, an element of nothing or a position under a case the row is
     * not at — or several values stand and none of them is the one. What is covered and what a
     * measurement is short of are different answers about a row, and only that one keeps them.
     */
    public ObservedValue valueAt(List<ObservedValue> inputs, TermPath path) {
        List<ObservedValue> values = valuesAt(inputs, path);
        return values != null && values.size() == 1 ? values.get(0) : null;
    }

    /**
     * One value on the way down a path, with the type the declaration puts there.
     *
     * <p>A list of these and not one, because a step into what a sequence holds turns one value
     * into as many as it holds. Everything else keeps the count it had.
     */
    private record Standing(ObservedValue value, Type type, TermPath reached,
                            Map<TermPath, Integer> at) {

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
                out.add(new Standing(here, type, reached, at));
                return true;
            }
            switch (step) {
                case TermPath.Step.Field named -> {
                    Type next = stepping(step, type, symbols);
                    if (next == null || !(here instanceof ObservedValue.Constructed made)) {
                        return false;
                    }
                    ObservedValue held = made.field(named.name());
                    if (held == null) {
                        return false;
                    }
                    out.add(new Standing(held, next, reached.then(named.name()), at));
                }
                // Every element the row wrote, and no choice among them. Which of them a rule is
                // about is not something the coordinate says, so what stands here is all of them
                // and what a class comes to over them is the caller's to decide. A list holding
                // none is a step taken: the walk arrived and the row wrote nothing there.
                case TermPath.Step.Element _ -> {
                    Type element = stepping(step, type, symbols);
                    if (element == null || !(here instanceof ObservedValue.Sequence written)) {
                        return false;
                    }
                    // Keyed by the step, which is this path with the step taken. Two positions
                    // that took it took the same one or they are not one reading of the row.
                    TermPath inside = reached.element();
                    for (int i = 0; i < written.elements().size(); i++) {
                        Map<TermPath, Integer> deeper = new java.util.LinkedHashMap<>(at);
                        deeper.put(inside, i);
                        out.add(new Standing(written.elements().get(i), element, inside, deeper));
                    }
                }
                // The value stays where it is and what may stand there narrows. A row whose value
                // does not meet the narrowing takes the step and stands nowhere below it — the
                // same answer a row writing the empty list gives at an element, and not the answer
                // a row nothing could read gives. What refuses the step is the type and the path
                // disagreeing about what is at this position, which is nothing about the row.
                case TermPath.Step.Refine refine -> {
                    Type narrowed = stepping(step, type, symbols);
                    if (narrowed == null) {
                        return false;
                    }
                    if (stands(refine.refinement(), here)) {
                        out.add(new Standing(here, narrowed, reached.refine(refine.refinement()),
                                at));
                    }
                }
            }
            return true;
        }

        /** Whether the value written here is one {@code refinement} leaves standing. */
        private static boolean stands(Refinement refinement, ObservedValue here) {
            return switch (refinement) {
                case Refinement.SumCase one -> switch (here) {
                    case ObservedValue.Unit unit -> one.leaf().equals(unit.type());
                    case ObservedValue.Constructed made -> one.leaf().equals(made.type());
                    default -> false;
                };
                case Refinement.Presence presence ->
                        presence.present() != (here instanceof ObservedValue.Absent);
            };
        }
    }
}
