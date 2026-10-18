package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.Location;
import souther.compiler.core.Core;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Where in an element the value a walk answered stands: the steps from the element to it.
 *
 * <p>What is left of a closure once it has been read. A {@code map} over a list answers, for each
 * element, some value made from it; where that value is a place inside the element, this is the way
 * there and the expression is not kept. Held as the expression, every reader of a run would be
 * reading a body the inliner happened to leave, and what may be read off one would grow with
 * whatever the inliner does next.
 *
 * <p>Relative, so it can be joined to whichever element position the run turns out to be over. The
 * closure was written about one element and the run is over all of them, and the two meet by this
 * being the part that does not depend on which.
 *
 * <p>Steps of a path and no other kind. A closure answering something built rather than something
 * read has no projection and is not one of these — which is what keeps a rule about what a branch
 * chose from being read as a rule about a field.
 */
public record ElementProjection(List<String> steps) {

    public ElementProjection {
        steps = List.copyOf(steps);
    }

    /**
     * What a closure whose parameter is {@code element} answered, as the way from the element to it,
     * or null where the answer is not read out of the element.
     *
     * <p>Read here and not where a position of the input is worked out. That reading asks which
     * position of a behavior's input an expression names and has the roots, the containers and the
     * provenance of elements to answer with; this one asks where inside one value another value
     * stands, and a name, a {@code let} and a field are the whole of what it takes. Answered by the
     * same walk, the steps that reach a behavior's parameters would be reachable from here, and the
     * relative way inside an element would quietly become an absolute one.
     *
     * <p><b>Null wherever the answer is not read out of the element.</b> A branch chooses between
     * two of them and is neither; arithmetic over one is a value the element does not hold; a
     * construction is something new, unless it is a newtype wearing one value of the element as
     * its name. None of those is a place a row writes, so a rule about what a
     * walk answered is not a rule about any position, and saying so is this reading's whole job on
     * that side.
     *
     * <p>Nothing here says the answer is one per element. That is a fact about the operation that
     * handed the closure its elements, proved where that operation stood; a caller wanting a run
     * needs both, and this is the half about the reading.
     *
     * @param held what each binding on the way holds, over the whole body the closure was left in
     */
    public static ElementProjection read(Core answer, BindingId element,
                                         Map<BindingId, Core> held,
                                         DeclarationNewtypes newtypes) {
        List<String> steps = new Reading(held, newtypes).from(answer, element);
        return steps == null ? null : new ElementProjection(steps);
    }

    /**
     * One reading of one closure's answer.
     *
     * <p>A value rather than a run of static calls, so that the bindings it is inside travel with
     * it. What stops it is that walk over the binding graph coming back to a binding it is already
     * answering ({@link BindingTrail}), which is the same law the reading of an input position
     * stops by — the one thing the two readings share.
     */
    private record Reading(Map<BindingId, Core> held, DeclarationNewtypes newtypes) {

        private Reading {
            if (newtypes == null) {
                throw new IllegalArgumentException("walking to an element asks which of the names"
                        + " on the way wrap one value, so it is handed somewhere to read that");
            }
        }

        private List<String> from(Core e, BindingId element) {
            return steps(e, element, new BindingTrail());
        }

        private List<String> steps(Core e, BindingId element, BindingTrail trail) {
            // Where an element stands does not turn on the type it stands as.
            return switch (Core.withoutStanding(e)) {
                // What a `let` comes to is what its body comes to, and the name it bound is answered
                // where it is read. Ordinary binding semantics, and what a helper applied to the
                // element leaves behind once it is spliced in: `amountOf(line).value` is a field of
                // a binding holding the element, and reading only the field would stop at the
                // splice.
                case Core.LetIn let -> steps(let.body(), element, trail);
                case Core.Read read -> {
                    if (element.equals(read.binding())) {
                        yield List.of();
                    }
                    Core through = held.get(read.binding());
                    yield through == null ? null
                            : trail.through(read.binding(),
                                    () -> steps(through, element, trail));
                }
                // The rule below a name at a time, along the names rather than down the stack.
                case Core.FieldProjection p -> {
                    List<String> base = steps(p.base(), element, trail);
                    if (base == null) {
                        yield null;
                    }
                    List<String> longer = new ArrayList<>(base);
                    Type from = p.base().type();
                    for (Core.FieldProjection.Step step : p.steps().inOrder()) {
                        if (Location.isStep(from, step.field(), newtypes)) {
                            longer.add(step.field());
                        }
                        from = step.type();
                    }
                    yield List.copyOf(longer);
                }
                case Core.FieldAccess fa -> {
                    List<String> base = steps(fa.target(), element, trail);
                    if (base == null) {
                        yield null;
                    }
                    if (!Location.isStep(fa.target().type(), fa.field(), newtypes)) {
                        yield base;
                    }
                    List<String> longer = new ArrayList<>(base);
                    longer.add(fa.field());
                    yield List.copyOf(longer);
                }
                // A newtype made of one value is that value wearing a name, so it stands where the
                // value does — the rule a position of the input is read by ({@link InputPath}).
                case Core.Construct construct when newtypes.of(construct.typeName().key())
                        && construct.values().size() == 1 ->
                        steps(construct.values().getFirst().value(), element, trail);
                case null, default -> null;
            };
        }
    }

    /**
     * The way to what {@code after} reaches from the value this reaches: where a walk answered this
     * of each element and a second walk answered {@code after} of each of those, the second's
     * answer stands at this way and then that one in the first walk's element.
     */
    public ElementProjection then(ElementProjection after) {
        List<String> longer = new ArrayList<>(steps);
        longer.addAll(after.steps);
        return new ElementProjection(longer);
    }

    /** The position this reaches from {@code element}. */
    public TermPath from(TermPath element) {
        TermPath at = element;
        for (String step : steps) {
            at = at.then(step);
        }
        return at;
    }

    /**
     * What stands at this way from {@code element}; where a value on the way was not read whole,
     * that value, which says what stopped it; and null only where a value read whole holds nothing
     * there.
     *
     * <p>Not read and not there are two answers. A reader handed none for both would read an
     * observation cut short as an element of another shape, which is a definite answer about the
     * row where the row said nothing; handed the value that stopped, it says what stopped as it
     * does for a value at the field itself.
     *
     * <p>A newtype is no step of a path, so a name wrapped round a record is walked through to the
     * record it wraps when a step is not one of its own fields.
     */
    public ObservedValue in(ObservedValue element) {
        ObservedValue at = element;
        for (String step : steps) {
            ObservedValue held = at;
            while (held.cause() == null && held instanceof ObservedValue.Constructed wrapper
                    && wrapper.field(step) == null && wrapper.field("value") != null) {
                held = wrapper.field("value");
            }
            if (held.cause() != null) {
                return held;
            }
            if (!(held instanceof ObservedValue.Constructed holder)) {
                return null;
            }
            at = holder.field(step);
            if (at == null) {
                return null;
            }
        }
        return at;
    }

    @Override
    public String toString() {
        return steps.isEmpty() ? "the element itself" : String.join(".", steps);
    }
}
