package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.Location;
import souther.compiler.core.ConstructionProjection;
import souther.compiler.core.Core;
import souther.compiler.inputs.OnePerElement.ReadOff;
import souther.compiler.inputs.OnePerElement.ReadOff.Taken;
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
     * construction is something new, though a field or a component read back out of one is the
     * value it was given. None of those is a place a row writes, so a rule about what a
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
        ReadOff found = new Reading(standing, held, newtypes, Licence.PLACE).from(answer, element);
        return found == null || found.placed() == null ? null : found.placed().at();
    }

    /**
     * What a closure whose parameter is {@code element} answered, as far as which answers are
     * equal goes: the value at a place of the element, or a newtype wearing it — or null where it
     * is neither ({@link Licence#EQUAL_KEY}).
     */
    static OnePerElement.Answered readAsAKey(Core answer, BindingId element,
                                            Map<BindingId, Core> held,
                                            DeclarationNewtypes newtypes) {
        ReadOff found = new Reading(Map.of(), held, newtypes, Licence.EQUAL_KEY)
                .from(answer, element);
        return found == null ? null : found.placed();
    }

    /**
     * What {@code read} takes out of what a closure whose parameter is {@code element} answered, as
     * far as which values are equal goes, as a way from the element — or null where that is
     * neither a way through what the element is nor a newtype wearing what it reaches.
     *
     * <p>The answer may be something built: a tuple or a record made of the element, which is no
     * place of it. What is taken out of one is what the construction was given for the part taken,
     * the same cancellation a field read back out of a construction is read by, so a component or a
     * field read where the walk was handed what the closure built is read where the closure was
     * handed the element. What is left of the read once no construction is there to take apart
     * goes on from where the answer stands in the element, and may still take a component out of
     * a tuple some walk beneath built. Read of the element itself ({@link ReadOff#ITSELF}), it is
     * the way the answer is read off the element.
     */
    static ReadOff readAsAKey(Core answer, ReadOff read, BindingId element,
                              Map<BindingId, Core> held, DeclarationNewtypes newtypes) {
        return new Reading(Map.of(), held, newtypes, Licence.EQUAL_KEY)
                .takenApart(answer, read, element);
    }

    /** Whether what a closure whose parameter is {@code element} answered is the element itself
     *  ({@link Licence#IDENTICAL_VALUE}). */
    static boolean isTheElementItself(Core answer, BindingId element, Map<BindingId, Core> held,
                                      DeclarationNewtypes newtypes) {
        ReadOff found = new Reading(Map.of(), held, newtypes, Licence.IDENTICAL_VALUE)
                .from(answer, element);
        return found != null && found.steps().isEmpty() && !found.wrapped();
    }

    /**
     * What a reading of an answer proves of it, which decides what it reads through.
     *
     * <p>Three questions over one walk. Names, {@code let}s and a field read back out of a
     * construction are crossed by all three: each leaves the value as it was. What else is
     * crossed is each one's to say, at every node and so behind a name as much as at the answer
     * itself.
     */
    private enum Licence {

        /** Where in the element the value stands, whatever type it stands as. */
        PLACE,

        /**
         * That answers are equal exactly where the values at a place of the element are. A
         * newtype wearing one value is read through and said to be, since two of them are equal
         * where the values are; a value standing as a wider type is not, since what the wider
         * type calls equal is not shown to be what the narrower one does.
         */
        EQUAL_KEY,

        /**
         * That the answer is the element itself. A field read, a newtype's {@code value} among
         * them, is another value; a newtype wearing the element, and the element standing as a
         * wider type, are other values of other types.
         */
        IDENTICAL_VALUE
    }

    /**
     * One reading of one closure's answer, for one licence.
     *
     * <p>A value rather than a run of static calls, so that the bindings it is inside travel with
     * it. What stops it is that walk over the binding graph coming back to a binding it is already
     * answering ({@link BindingTrail}), which is the same law the reading of an input position
     * stops by — the one thing the two readings share.
     */
    private record Reading(Map<BindingId, ElementProjection> standing, Map<BindingId, Core> held,
                           DeclarationNewtypes newtypes, Licence licence) {

        private Reading {
            if (newtypes == null) {
                throw new IllegalArgumentException("walking to an element asks which of the names"
                        + " on the way wrap one value, so it is handed somewhere to read that");
            }
        }

        private ReadOff from(Core e, BindingId element) {
            return steps(e, element, new BindingTrail());
        }

        private ReadOff takenApart(Core e, ReadOff read, BindingId element) {
            BindingTrail trail = new BindingTrail();
            Core at = e;
            List<Taken> within = read.steps();
            int taken = 0;
            while (taken < within.size()
                    && given(at, within.get(taken), trail) instanceof Core given) {
                at = given;
                taken++;
            }
            ReadOff base = steps(at, element, trail);
            if (base == null) {
                return null;
            }
            List<Taken> longer = new ArrayList<>(base.steps());
            longer.addAll(within.subList(taken, within.size()));
            return new ReadOff(longer, base.wrapped() || read.wrapped());
        }

        private ReadOff steps(Core e, BindingId element, BindingTrail trail) {
            return switch (e) {
                // Where an element stands does not turn on the type it stands as; what is equal
                // and what is the same value do.
                case Core.Widen wider -> licence == Licence.PLACE
                        ? steps(wider.value(), element, trail) : null;
                // What a `let` comes to is what its body comes to, and the name it bound is answered
                // where it is read. Ordinary binding semantics, and what a helper applied to the
                // element leaves behind once it is spliced in: `amountOf(line).value` is a field of
                // a binding holding the element, and reading only the field would stop at the
                // splice.
                case Core.LetIn let -> steps(let.body(), element, trail);
                case Core.Read read -> {
                    if (element.equals(read.binding())) {
                        yield ReadOff.ITSELF;
                    }
                    // A name an arm bound is the value it matched, at the case the arm took.
                    ElementProjection matched = standing.get(read.binding());
                    if (matched != null) {
                        yield ReadOff.ITSELF.after(new OnePerElement.Answered(matched, false));
                    }
                    Core through = held.get(read.binding());
                    yield through == null ? null
                            : trail.through(read.binding(),
                                    () -> steps(through, element, trail));
                }
                // The rule below a name at a time, along the names rather than down the stack.
                case Core.FieldProjection p -> {
                    List<Core.FieldProjection.Step> along = p.steps().inOrder();
                    Core read = p.base();
                    Type from = p.base().type();
                    int next = 0;
                    while (next < along.size()) {
                        Core given = given(read, field(along.get(next).field()), trail);
                        if (given == null) {
                            break;
                        }
                        read = given;
                        from = along.get(next).type();
                        next++;
                    }
                    ReadOff base = steps(read, element, trail);
                    if (base == null || next == along.size()) {
                        yield base;
                    }
                    if (licence == Licence.IDENTICAL_VALUE) {
                        yield null;
                    }
                    List<Taken> longer = new ArrayList<>(base.steps());
                    for (Core.FieldProjection.Step step : along.subList(next, along.size())) {
                        if (Location.isStep(from, step.field(), newtypes)) {
                            longer.add(field(step.field()));
                        }
                        from = step.type();
                    }
                    yield new ReadOff(longer, base.wrapped());
                }
                // A field of a construction is the value the construction was given for it, which
                // is where that value stands.
                case Core.FieldAccess fa when given(fa.target(), field(fa.field()), trail)
                        instanceof Core given -> steps(given, element, trail);
                case Core.FieldAccess fa -> {
                    ReadOff base = licence == Licence.IDENTICAL_VALUE ? null
                            : steps(fa.target(), element, trail);
                    if (base == null) {
                        yield null;
                    }
                    if (!Location.isStep(fa.target().type(), fa.field(), newtypes)) {
                        yield base;
                    }
                    List<Taken> longer = new ArrayList<>(base.steps());
                    longer.add(field(fa.field()));
                    yield new ReadOff(longer, base.wrapped());
                }
                // A component of a tuple is the value the tuple was given for it, as a field of a
                // construction is.
                case Core.TupleGet get when given(get.tuple(), new Taken.Component(get.index()),
                        trail) instanceof Core given -> steps(given, element, trail);
                // A component of a tuple standing in the element is another value, and stands at
                // no place of the input, since no input holds a tuple: the way goes on through it,
                // and a reading asking for a place says it comes to none.
                case Core.TupleGet get -> {
                    ReadOff base = licence == Licence.IDENTICAL_VALUE ? null
                            : steps(get.tuple(), element, trail);
                    if (base == null) {
                        yield null;
                    }
                    List<Taken> longer = new ArrayList<>(base.steps());
                    longer.add(new Taken.Component(get.index()));
                    yield new ReadOff(longer, base.wrapped());
                }
                // A newtype of one value is a name the value wears: equal where the value is, and
                // not the value.
                case Core.Construct made when licence == Licence.EQUAL_KEY
                        && newtypes.of(made.typeName().key()) && made.values().size() == 1 -> {
                    ReadOff worn = steps(made.values().getFirst().value(), element, trail);
                    yield worn == null ? null : new ReadOff(worn.steps(), true);
                }
                case null, default -> null;
            };
        }

        /**
         * What the construction {@code e} stands for was given for the part {@code step} takes
         * out of it — a field of a record, a component of a tuple — or null where {@code e} stands
         * for no such construction this reaches: the same cancellation a position of the input is
         * read by ({@link ConstructionProjection#given}).
         */
        private Core given(Core e, Taken step, BindingTrail trail) {
            return switch (e) {
                case Core.Widen wider -> licence == Licence.PLACE
                        ? given(wider.value(), step, trail) : null;
                case Core.Construct made when step instanceof Taken.Inside(
                        TermPath.Step.Field(String field)) ->
                        ConstructionProjection.given(made, field);
                case Core.Tuple tuple when step instanceof Taken.Component(int index) ->
                        index < tuple.elements().size() ? tuple.elements().get(index) : null;
                case Core.LetIn let -> given(let.body(), step, trail);
                case Core.Read read -> {
                    Core through = held.get(read.binding());
                    yield through == null ? null
                            : trail.through(read.binding(), () -> given(through, step, trail));
                }
                // A construction whose part was given another construction, a name at a time.
                case Core.FieldAccess fa -> {
                    Core inner = given(fa.target(), field(fa.field()), trail);
                    yield inner == null ? null : given(inner, step, trail);
                }
                case Core.TupleGet get -> {
                    Core inner = given(get.tuple(), new Taken.Component(get.index()), trail);
                    yield inner == null ? null : given(inner, step, trail);
                }
                case Core.FieldProjection p -> {
                    Core inner = p.base();
                    for (Core.FieldProjection.Step each : p.steps().inOrder()) {
                        inner = given(inner, field(each.field()), trail);
                        if (inner == null) {
                            break;
                        }
                    }
                    yield inner == null ? null : given(inner, step, trail);
                }
                case null, default -> null;
            };
        }

        private static Taken field(String name) {
            return new Taken.Inside(new TermPath.Step.Field(name));
        }
    }

    /**
     * The way to what {@code after} reaches from the value this reaches: where a walk answered this
     * of each element and a second walk answered {@code after} of each of those, the second's
     * answer stands at this way and then that one in the first walk's element.
     */
    public ElementProjection then(ElementProjection after) {
        List<TermPath.Step> longer = new ArrayList<>(steps);
        longer.addAll(after.steps);
        return new ElementProjection(longer);
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
