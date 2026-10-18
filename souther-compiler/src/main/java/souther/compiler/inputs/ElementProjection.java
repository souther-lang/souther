package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.Location;
import souther.compiler.core.Core;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

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
 *
 * <p>Fields, and the narrowings an arm of a {@code match} on the element takes, and nothing that
 * goes into a container: the way stays inside one element. A narrowing is a step for the reason it
 * is one of {@link TermPath}: {@code @A.amount} and {@code @B.amount} are two places, each with
 * the type and the rules its case declares, and written as the name {@code amount} alone they would
 * be one.
 */
public record ElementProjection(List<TermPath.Step> steps) {

    public ElementProjection {
        steps = List.copyOf(steps);
        for (TermPath.Step step : steps) {
            if (!staysInside(step)) {
                throw new IllegalArgumentException("a way inside one element goes into no"
                        + " container, and " + step + " does");
            }
        }
    }

    /**
     * Whether {@code step} stays inside one element: a field, or a narrowing.
     *
     * <p>Exhaustive over {@link TermPath.Step}, with no {@code default}, so a step added later is
     * put on one side of this here and not on whichever side each reader's test left it.
     */
    private static boolean staysInside(TermPath.Step step) {
        return switch (step) {
            case TermPath.Step.Field _, TermPath.Step.Refine _ -> true;
            case TermPath.Step.Element _, TermPath.Step.Key _ -> false;
        };
    }

    /** The way through {@code fields}, one after another. */
    public static ElementProjection ofFields(List<String> fields) {
        return new ElementProjection(
                fields.stream().map(each -> (TermPath.Step) new TermPath.Step.Field(each)).toList());
    }

    /**
     * The way from the element at {@code element} to {@code place}, or null where {@code place} is
     * not reached from it by fields and narrowings alone.
     */
    public static ElementProjection below(TermPath element, TermPath place) {
        if (!place.isAtOrUnder(element)) {
            return null;
        }
        List<TermPath.Step> steps = place.steps().subList(element.steps().size(),
                place.steps().size());
        return steps.stream().allMatch(ElementProjection::staysInside)
                ? new ElementProjection(steps) : null;
    }

    /** The names of the fields this goes through, where it goes through fields alone, or null where
     *  a narrowing is on the way. */
    public List<String> fields() {
        List<String> names = new ArrayList<>();
        for (TermPath.Step step : steps) {
            if (!(step instanceof TermPath.Step.Field field)) {
                return null;
            }
            names.add(field.name());
        }
        return List.copyOf(names);
    }

    /** The same way, one field further in. */
    public ElementProjection then(String field) {
        List<TermPath.Step> longer = new ArrayList<>(steps);
        longer.add(new TermPath.Step.Field(field));
        return new ElementProjection(longer);
    }

    /** The same place, narrowed to the values {@code cases} leaves. */
    public ElementProjection narrowedTo(CasesLeft cases) {
        List<TermPath.Step> longer = new ArrayList<>(steps);
        longer.add(new TermPath.Step.Refine(cases));
        return new ElementProjection(longer);
    }

    /** The place this narrows, where its last step is a narrowing, or null where it is not. */
    public ElementProjection narrowedFrom() {
        return steps.isEmpty() || !(steps.getLast() instanceof TermPath.Step.Refine) ? null
                : new ElementProjection(steps.subList(0, steps.size() - 1));
    }

    /** What the last step leaves the value, where it is a narrowing, or null where it is not. */
    public CasesLeft narrowing() {
        return !steps.isEmpty() && steps.getLast() instanceof TermPath.Step.Refine(CasesLeft cases)
                ? cases : null;
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
     * construction is something new. None of those is a place a row writes, so a rule about what a
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
        return read(answer, element, Map.of(), held, newtypes);
    }

    /**
     * The same, inside arms of a {@code match} on the element: each name an arm bound stands for
     * the value it matched, read as the case the arm took, which is a place of the element.
     *
     * @param standing where in the element each name an arm on the way bound stands
     */
    public static ElementProjection read(Core answer, BindingId element,
                                         Map<BindingId, ElementProjection> standing,
                                         Map<BindingId, Core> held,
                                         DeclarationNewtypes newtypes) {
        List<TermPath.Step> steps = new Reading(standing, held, newtypes).from(answer, element);
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
    private record Reading(Map<BindingId, ElementProjection> standing, Map<BindingId, Core> held,
                           DeclarationNewtypes newtypes) {

        private Reading {
            if (newtypes == null) {
                throw new IllegalArgumentException("walking to an element asks which of the names"
                        + " on the way wrap one value, so it is handed somewhere to read that");
            }
        }

        private List<TermPath.Step> from(Core e, BindingId element) {
            return steps(e, element, new BindingTrail());
        }

        private List<TermPath.Step> steps(Core e, BindingId element, BindingTrail trail) {
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
                    ElementProjection matched = standing.get(read.binding());
                    if (matched != null) {
                        yield matched.steps();
                    }
                    Core through = held.get(read.binding());
                    yield through == null ? null
                            : trail.through(read.binding(),
                                    () -> steps(through, element, trail));
                }
                // The rule below a name at a time, along the names rather than down the stack.
                case Core.FieldProjection p -> {
                    List<TermPath.Step> base = steps(p.base(), element, trail);
                    if (base == null) {
                        yield null;
                    }
                    List<TermPath.Step> longer = new ArrayList<>(base);
                    Type from = p.base().type();
                    for (Core.FieldProjection.Step step : p.steps().inOrder()) {
                        if (Location.isStep(from, step.field(), newtypes)) {
                            longer.add(new TermPath.Step.Field(step.field()));
                        }
                        from = step.type();
                    }
                    yield List.copyOf(longer);
                }
                case Core.FieldAccess fa -> {
                    List<TermPath.Step> base = steps(fa.target(), element, trail);
                    if (base == null) {
                        yield null;
                    }
                    if (!Location.isStep(fa.target().type(), fa.field(), newtypes)) {
                        yield base;
                    }
                    List<TermPath.Step> longer = new ArrayList<>(base);
                    longer.add(new TermPath.Step.Field(fa.field()));
                    yield List.copyOf(longer);
                }
                case null, default -> null;
            };
        }
    }

    /** The position this reaches from {@code element}. */
    public TermPath from(TermPath element) {
        TermPath at = element;
        for (TermPath.Step step : steps) {
            at = switch (step) {
                case TermPath.Step.Field field -> at.then(field.name());
                case TermPath.Step.Refine refine -> at.refine(refine.cases());
                case TermPath.Step.Element _, TermPath.Step.Key _ ->
                        throw new IllegalStateException("a way inside one element goes into no"
                                + " container");
            };
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
     * <p>A newtype is no step of a path, so a value on the way may be written inside the names it
     * wears. Before each step the names the declaration puts at the place reached so far come off
     * ({@link ObservedValue#inside}), by name: which names a place wears is the declaration's to
     * say, and a value's shape does not say it — a record may have a field of its own called
     * {@code value}.
     *
     * <p>A narrowing goes nowhere and is passed where the value is a case it leaves. A value of
     * another case holds nothing below it, which is the element's own answer and not one cut short.
     *
     * @param wornAt the names the declaration puts at each place on the way, from the element itself
     *               to the one before the last step
     */
    public ObservedValue in(ObservedValue element,
                            Function<ElementProjection, List<TypeSymbol>> wornAt) {
        ObservedValue at = element;
        for (int i = 0; i < steps.size(); i++) {
            at = ObservedValue.inside(wornAt.apply(new ElementProjection(steps.subList(0, i))), at);
            if (at.cause() != null) {
                return at;
            }
            switch (steps.get(i)) {
                case TermPath.Step.Refine(CasesLeft cases) -> {
                    if (!cases.leaves(at)) {
                        return null;
                    }
                }
                case TermPath.Step.Field(String field) -> {
                    if (!(at instanceof ObservedValue.Constructed holder)) {
                        return null;
                    }
                    at = holder.field(field);
                    if (at == null) {
                        return null;
                    }
                }
                case TermPath.Step.Element _, TermPath.Step.Key _ ->
                        throw new IllegalStateException("a way inside one element goes into no"
                                + " container");
            }
        }
        return at;
    }

    /** Every place on the way to this from the element, the element itself first and this last. */
    public List<ElementProjection> onTheWay() {
        List<ElementProjection> out = new ArrayList<>();
        for (int i = 0; i <= steps.size(); i++) {
            out.add(new ElementProjection(steps.subList(0, i)));
        }
        return out;
    }

    @Override
    public String toString() {
        return steps.isEmpty() ? "the element itself" : spelled();
    }

    /** The way as a path below an element writes it, {@code kind@A.amount}, and nothing for the
     *  element itself. */
    public String spelled() {
        StringBuilder out = new StringBuilder();
        for (TermPath.Step step : steps) {
            if (step instanceof TermPath.Step.Field && !out.isEmpty()) {
                out.append('.');
            }
            out.append(step);
        }
        return out.toString();
    }
}
