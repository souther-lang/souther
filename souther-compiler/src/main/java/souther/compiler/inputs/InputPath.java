package souther.compiler.inputs;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.CallArguments;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.Location;
import souther.compiler.core.ConstructionProjection;
import souther.compiler.core.Core;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.MapPart;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * Which position of a behavior's input an expression names, and that it names none where it names
 * none ({@link PathResolution}).
 *
 * <p>One answer, for every reader of a body that has something to say about a position. A
 * {@code guard} comparing a field, a {@code match} on a parameter and an arm declaring a case
 * cannot arrive are three statements about the same positions, and each working out for itself
 * which position it was talking about is three spellings of one path — of which the axes carry one,
 * so the other two would be about positions nothing measures.
 *
 * <p><b>Asked of the binding and never of the spelling.</b> A body may bind a name its own behavior
 * already binds, and the two are different values under one word: {@code let f = defaulted(f)}
 * leaves every read below it naming the local, whose values are whatever the call answers with.
 * Read by name, the reads below it are the parameter's, and what is said about the parameter's rules
 * is said about a value they never reached ({@link BindingId} states this for every reader at once).
 *
 * <p><b>Two kinds of step and no third.</b> Descending an expression — a field's target, a call's
 * argument — stays inside one finite tree and needs nothing to stop it. Crossing to another
 * expression goes through a binding: what a name holds, what handed a name the elements of a
 * container, which binding another's elements are the same as. Those steps are a walk over the
 * binding graph and {@link BindingTrail} is the whole of what stops them, so a step added here is
 * one of the two and never a share of somebody's allowance. Nothing counts how far a walk has come:
 * a count of how many names a reading may pass through is a count of how a model was written, and
 * one name more than it allows is a position this reports as one nothing names.
 *
 * <p><b>What a name is decides which step is taken, and one step is taken.</b> A binding is a
 * parameter, or what an operation handed an element of a container on, or what a name was given, in
 * that order and asked once ({@link BindingRole}). A binding can be more than one: two walks over one
 * collection joined into one leave the second walk's element bound to what the first walk's closure
 * made. Tried as roads and raced, the winner is whichever reaches a position, and there it is the
 * value the rewrite left under the name — a rule about a value <em>made from</em> a position read as
 * a rule about the position. So an element is answered by its container and by nothing beside it,
 * whatever that answer comes to.
 *
 * <p>An expression that binds a name of its own is descended under that name. That is what a
 * {@code let} means, and it is what a helper applied to an argument is left as; a shape a splice
 * happens to leave is not a reason to stop, and stopping there left every claim inside an expanded
 * helper about a position nothing here could name.
 *
 * <p>What is known of the names comes in as answers and nothing else ({@link BindingEnvironment}).
 * How many names there are is not a fact about how far a value's provenance runs — a name bound in
 * an arm is read under bindings written elsewhere — and a reading of what a name means is built on
 * this one rather than beside it, so neither is something a walk here can reach for.
 *
 * <p>Nothing about the reading of an input reaches this and nothing here reaches it: what a position
 * can hold is read from the declarations ({@link InputDomain}), and this only says which position an
 * expression is pointing at.
 */
final class InputPath {

    private final DeclarationNewtypes newtypes;
    private final ElementQuestion asked;
    /** What the reading this walk is asked on takes a node as ({@link InputReads#taking}). */
    private final Function<Core, Denotation> taken;
    private final BindingTrail trail = new BindingTrail();
    /** The direction a walk after the order must come out walking ({@link TraversalDirection});
     *  the other questions say nothing of it. */
    private final TraversalDirection arrivingAs;
    /** The direction the elements are handed in at the expression the walk is at, relative to the
     *  position it is walking towards: turned over by every operation crossed that answers its
     *  list the other way round, and put back as the walk comes out of it. */
    private TraversalDirection walking = TraversalDirection.FORWARD;

    private InputPath(DeclarationNewtypes newtypes, ElementQuestion asked,
                      Function<Core, Denotation> taken) {
        this(newtypes, asked, taken, TraversalDirection.FORWARD);
    }

    private InputPath(DeclarationNewtypes newtypes, ElementQuestion asked,
                      Function<Core, Denotation> taken, TraversalDirection arrivingAs) {
        this.newtypes = newtypes;
        this.asked = asked;
        this.taken = taken;
        this.arrivingAs = arrivingAs;
    }

    /**
     * {@code e} where the reading takes it as another value: that value, read where it was given,
     * by a walk asking the same question there — or null where it is not taken. A node taken is
     * the value on that reading wherever it is reached from, so the container a choice answered on
     * the arm a reading is on is the container an element handed from it is in.
     */
    private PathResolution whereTaken(Core e, Wanted wanted) {
        Denotation as = taken.apply(e);
        if (as == null || Core.withoutStanding(as.value()) == Core.withoutStanding(e)) {
            return null;
        }
        InputPath there = new InputPath(newtypes, asked, as.at()::taken, arrivingAs);
        there.walking = walking;
        return wanted == null ? there.named(as.value(), as.at().names())
                : there.heldAt(as.value(), wanted, as.at().names());
    }

    /**
     * The position {@code e} names, read where {@code reads} has got to.
     *
     * <p>Which fields are steps is {@link Location}'s rule, asked here rather than restated: a
     * newtype's {@code value} is not one, so {@code request.cost} and {@code request.cost.value}
     * are one position, and if the two spellings disagreed the same position would become two axes,
     * one of which no row would ever cover.
     *
     * <p>The root is the parameter as the behavior declares it. What a behavior takes is what it
     * declares, and a declared parameter is not a binding — a behavior with no implementation has
     * positions all the same — so a path is rooted at the declaration and {@link Location} at the
     * binding a body gave it.
     *
     * <p>Through what a run of {@code let}s bound on the way, since what a {@code let} binds is
     * evaluated on the way to the answer: a body that names its argument and then matches the name
     * is matching the argument. That is what a helper expanded into a body looks like, and reading
     * only the outermost name would leave every claim inside an expanded helper about a position
     * nothing here can name.
     */
    static PathResolution of(Core e, BindingEnvironment names, DeclarationNewtypes newtypes,
                             Function<Core, Denotation> taken) {
        return new InputPath(newtypes, ElementQuestion.NAMED_POSITION, taken).named(e, names);
    }

    /**
     * Where {@code e}'s value came from, and that it came from none where it did.
     *
     * <p>Beside {@link #of} and a different question, not a wider or a narrower one. That one
     * answers which position an expression names, and what a row writes at a position is what a rule
     * about it is about; this answers where a value came from. So the two cross different edges: an
     * edge saying these elements were made from another binding's is one this goes on through and
     * one that must stop, and a value made from a position is not that position — a rule about it is
     * not a rule about the values there, and nothing here says what it comes to for them.
     *
     * <p>So what this is for is saying that a rule was written. An author who filters what a
     * {@code map} answered wrote a comparison, and a reading that could place it nowhere said
     * nothing at all — which reads as a model with no rule there rather than a rule this could not
     * follow.
     */
    static PathResolution cameFrom(Core e, BindingEnvironment names,
                                   DeclarationNewtypes newtypes,
                                   Function<Core, Denotation> taken) {
        return new InputPath(newtypes, ElementQuestion.VALUE_ORIGIN, taken).named(e, names);
    }

    /**
     * Where an element handed to {@code binding} stands, and that it stands at none where it does.
     *
     * <p>What an operation of the language hands its closure is an element of the container it was
     * given, so the name it arrives under stands at that container's position, inside it. Asked of
     * the binding rather than of the container's expression: a container built by one operation and
     * handed to the next names no position of its own, and the elements are the same elements.
     */
    static PathResolution elementAt(BindingId binding, BindingEnvironment names,
                                    DeclarationNewtypes newtypes,
                                    Function<Core, Denotation> taken) {
        return new InputPath(newtypes, ElementQuestion.NAMED_POSITION, taken)
                .elementOf(binding, names);
    }

    /**
     * The position whose every occurrence {@code e} holds the values of, each as often, and that it
     * holds those of none where it does not.
     *
     * <p>Beside {@link #of} and the stronger question. That one answers which position an
     * expression names, and an expression that keeps some of what a container holds names the
     * container's. A total over the values wants more: that nothing standing at the position is
     * left out and nothing is counted twice. So this crosses only what puts the elements in another
     * order, answers each as it is, or puts the elements of what a closure answered end to end, and
     * starts only at a container no other container holds — a list inside the elements of another
     * holds some of the occurrences of its path, and the path says no more than the whole of them.
     *
     * @return the position of the elements of {@code e}
     */
    static PathResolution everyElementOf(Core e, BindingEnvironment names,
                                         DeclarationNewtypes newtypes,
                                         Function<Core, Denotation> taken) {
        return new InputPath(newtypes, ElementQuestion.EVERY_OCCURRENCE, taken)
                .heldAt(e, new Wanted.APart(HeldIn.Part.ELEMENT), names).heldAt();
    }

    /** The same, of the elements handed to {@code binding}. */
    static PathResolution everyElementAt(BindingId binding, BindingEnvironment names,
                                         DeclarationNewtypes newtypes,
                                         Function<Core, Denotation> taken) {
        return new InputPath(newtypes, ElementQuestion.EVERY_OCCURRENCE, taken)
                .elementOf(binding, names).heldAt();
    }

    /**
     * The position whose every occurrence the elements handed to {@code binding} are, once each and
     * handed in {@code direction} — the order the row writes them there, or the opposite — and that
     * they are those of none where they are not ({@link ElementQuestion#IN_THE_ORDER_WRITTEN}).
     *
     * <p>Beside {@link #everyElementAt} and stronger again. The only operations crossed are those
     * declared to answer a list the other way round, each turning the direction over, so two of them
     * are the order written; a reordering of any other kind or a filter says nothing of the order,
     * and the walk stops at it.
     */
    static PathResolution inTheOrderAt(BindingId binding, TraversalDirection direction,
                                       BindingEnvironment names, DeclarationNewtypes newtypes,
                                       Function<Core, Denotation> taken) {
        return new InputPath(newtypes, ElementQuestion.IN_THE_ORDER_WRITTEN, taken, direction)
                .elementOf(binding, names).heldAt();
    }

    /** Whether the question in hand wants every occurrence of a position, each once. */
    private boolean asksEveryOccurrence() {
        return switch (asked) {
            case EVERY_OCCURRENCE, IN_THE_ORDER_WRITTEN -> true;
            case NAMED_POSITION, VALUE_ORIGIN, ONE_PER_ELEMENT, SAME_EMPTINESS -> false;
        };
    }

    private PathResolution named(Core e, BindingEnvironment names) {
        PathResolution where = whereTaken(e, null);
        if (where != null) {
            return where;
        }
        return switch (e) {
            // What the name is, asked once, and the step that answers is the answer. An element is
            // answered by the container it came from even where that container is at no position:
            // the value a rewrite left under such a name is what the walk before it made of an
            // element, and reaching a position through it would put a line at a place whose values
            // are not the ones a rule about the name is about.
            case Core.Read r -> switch (names.roleOf(r.binding())) {
                case BindingRole.Root(var stands) -> new PathResolution.At(stands);
                case BindingRole.Element _ -> elementOf(r.binding(), names);
                // An element of more than one container is at one of their places and which is not
                // settled. Answered with the first, a rule under this name would be filed at a
                // container it says nothing about; answered with none, it would read as a name that
                // holds nothing of the input, and a rule the author wrote about their input would
                // leave the measurement without a word.
                case BindingRole.ElementOfSeveral(var containers) ->
                        oneOfTheElementsOf(r.binding(), containers, names);
                case BindingRole.Alias(var held) ->
                        trail.through(r.binding(), () -> named(held, names));
                case BindingRole.Unknown _ -> new PathResolution.NotAPosition();
            };
            // A projection out of a construction is the value that field was given, and it is that
            // value's position that is asked for. The construction and the projection cancel: what
            // the input holds at the position is what was handed in, and a field of it read back out
            // is the same value under another name. Asked as a path of the construction instead, the
            // answer is that a value built here is at no position — which is true of the
            // construction and is not what the projection above it reads.
            case Core.FieldAccess fa when introducing(fa.target(), names,
                    (construct, at) -> named(given(construct, fa), at))
                    instanceof PathResolution reduced -> reduced;
            // A field of what the target stands at, at every place the target stands. Where the
            // field is not a step of a path — a newtype's own value is the value under it — the
            // place is the target's, which is the step this takes there.
            case Core.FieldAccess fa -> named(fa.target(), names).deeper(
                    // Asked of {@link Location}, which owns the rule, from the answer this walk was
                    // handed. Whether a name wears one value was settled when the module was
                    // indexed, so a path through a field does not turn on what the declaration
                    // says or on where it is written.
                    Location.isStep(fa.target().type(), fa.field(), newtypes)
                            ? base -> base.then(fa.field()) : base -> base);
            // The two rules above a name at a time, from the base.
            case Core.FieldProjection p -> namedAlong(p.base(), p.steps().inOrder(), 0, names);
            // A newtype made of one value is that value wearing a name, so it stands where the value
            // does: the other way round from reading its `value`, which is no step either. Read as
            // no position, `Slug(draft.title)` handed to a dependency asked it about nothing a row
            // writes, where `draft.title` asked it about a position.
            case Core.Construct construct when newtypes.of(construct.typeName().key())
                    && construct.values().size() == 1 ->
                    named(construct.values().getFirst().value(), names);
            // What an expression that binds a name comes to is what its body comes to, under that
            // name. Whether the name may stand for the position its value names is not asked here
            // and is not a question about this shape: it is asked where the name is read, of what
            // the name is.
            case Core.LetIn let -> named(let.body(), names.inside(let.binder(), let.value()));
            // A value standing as a wider type is at the place it is at.
            case Core.Widen w -> named(w.value(), names);
            // A call kept standing names no location. Where the walk is over a tree that keeps them
            // that is the answer, and where it is not, its presence says this walk was handed a
            // representation it does not read — said rather than answered with "no path", which
            // would be the same answer a number gives.
            case Core.PreservedCall p -> {
                if (!names.callsStand()) {
                    throw p.unexpectedIn("an input position");
                }
                yield new PathResolution.NotAPosition();
            }
            // And every other shape names no position, said one at a time. A shape swallowed by a
            // default would come back as a model that states nothing, which is what a reader acts
            // on — so a shape added to the language is one this does not compile without.
            //
            // A value written out. The input holds it nowhere; it is what a body put beside what the
            // input holds.
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _,
                 Core.UnitValue _, Core.ListLit _, Core.Tuple _, Core.OptionSome _,
                 Core.OptionNone _, Core.Construct _, Core.MaterialisedValue _ ->
                    new PathResolution.NotAPosition();
            // A value made from others. What arithmetic and what an operation answered came from
            // positions and are not positions, which is a reading of its own
            // ({@link #cameFrom}).
            case Core.Neg _, Core.Binary _, Core.Call _, Core.Apply _ ->
                    new PathResolution.NotAPosition();
            // A choice between values, which stands at no one place.
            case Core.If _, Core.IfConstructed _, Core.Match _ -> new PathResolution.NotAPosition();
            // A place inside a tuple is no position of an input of its own: what a path is made of
            // is a field, what a container holds, a key and a case ({@link TermPath.Step}). Where
            // the tuple is an entry of a map a walk was handed, its places are that map's key and
            // value, and that is the container's to say.
            case Core.TupleGet get -> placeOf(get, names);
            // A closure is a value the language hands an operation, and what it answers about an
            // element is read where the operation stood ({@link ElementProjection}).
            case Core.Block _ -> new PathResolution.NotAPosition();
            // A place no row arrives at holds no value to be about.
            case Core.Unreachable _ -> new PathResolution.NotAPosition();
            // Nothing at all, which a caller may hand over where a body has no expression there.
            case null -> new PathResolution.NotAPosition();
        };
    }

    /**
     * What a reader makes of a construction and the names it stands under.
     *
     * <p>Two values because a construction reached through a {@code let} is written under bindings
     * the expression above it is not: the value a field of it was given is read where the
     * construction is, and read where the projection stands, a name the {@code let} opened would
     * stand for nothing.
     *
     * @param <T> what that reader answers
     */
    private interface OfAConstruction<T> {
        T of(Core.Construct construct, BindingEnvironment names);
    }

    /**
     * What {@code found} makes of the construction {@code e} stands for, or null where {@code e}
     * stands for none this walk reaches.
     *
     * <p>Which value a name holds is asked of the environment the same way the answer about a position
     * is, and by the same steps: a name that was given a value, a {@code let}'s body, and a projection
     * already reduced. What is not asked is where the construction stands — that question is the one
     * whose answer this exists to get right, and asked here it would be answered for the construction
     * rather than for the field read out of it.
     *
     * <p><b>The reader runs inside the walk and not after it.</b> Crossing to what a name holds is a
     * step over the binding graph, and what keeps such a walk acyclic holds a binding only while the
     * walk that crossed it is going on ({@link BindingTrail}). Reading the value a field was given is
     * part of that walk: it is where the way back to the binding runs, since what the field was given
     * may read the name again. Handed back as a value and read after the crossing, the binding is off
     * the way while its own value is being followed, and a construction holding a read of the name it
     * is bound to runs until the stack is gone rather than being raised as the graph this compiler
     * does not build. So the answer is taken here, under every binding on the way to it.
     *
     * <p>Descending from a construction to the value it gave a field needs nothing of its own: that
     * stays inside one expression, which is the kind of step nothing has to bound.
     */
    private <T> T introducing(Core e, BindingEnvironment names, OfAConstruction<T> found) {
        return switch (Core.withoutStanding(e)) {
            case Core.Construct construct -> found.of(construct, names);
            case Core.Read r when names.roleOf(r.binding()) instanceof BindingRole.Alias(var held) ->
                    trail.through(r.binding(), () -> introducing(held, names, found));
            case Core.LetIn let ->
                    introducing(let.body(), names.inside(let.binder(), let.value()), found);
            // A projection of a construction whose field was given another construction, which is
            // what a value built out of values written where they stand looks like.
            case Core.FieldAccess fa -> introducing(fa.target(), names,
                    (construct, at) -> introducing(given(construct, fa), at, found));
            case Core.FieldProjection p ->
                    introducingAlong(p.base(), p.steps().inOrder(), 0, names, found);
            case null, default -> null;
        };
    }

    /**
     * What {@code fa} reads out of {@code construct}.
     *
     * <p>Never nothing: a construction holds every declared field and a projection names a field of
     * the type it reads, so a construction without the field asked for is this compiler disagreeing
     * with itself and is said where it is found.
     */
    private static Core given(Core.Construct construct, Core.FieldAccess fa) {
        return given(construct, fa.field());
    }

    private static Core given(Core.Construct construct, String field) {
        Core written = ConstructionProjection.given(construct, field);
        if (written == null) {
            throw new IllegalStateException("a construction of " + construct.typeName()
                    + " was read for a field it has none of: " + field);
        }
        return written;
    }

    /**
     * Where the value {@code steps} from {@code next} on read off {@code from} stands: the two
     * rules for a field access, asked a name at a time.
     *
     * <p>A construction the names start from cancels against the first of them, and what that field
     * was given is read on. Where none does, each name is one more step of where {@code from}
     * stands, taken along the names: how many there are is as long as the declarations chain, and
     * only a cancellation — which is as deep as the constructions the source wrote — goes down the
     * stack.
     */
    private PathResolution namedAlong(Core from, List<Core.FieldProjection.Step> steps, int next,
                                      BindingEnvironment names) {
        PathResolution reduced = introducing(from, names, (construct, at) -> {
            Core given = given(construct, steps.get(next).field());
            return next + 1 == steps.size() ? named(given, at)
                    : namedAlong(given, steps, next + 1, at);
        });
        if (reduced != null) {
            return reduced;
        }
        PathResolution at = named(from, names);
        Type read = from.type();
        for (int i = next; i < steps.size(); i++) {
            Core.FieldProjection.Step step = steps.get(i);
            at = at.deeper(Location.isStep(read, step.field(), newtypes)
                    ? base -> base.then(step.field()) : base -> base);
            read = step.type();
        }
        return at;
    }

    /** What {@code found} makes of the construction the value {@code steps} from {@code next} on
     *  read off {@code from} stands for, each name cancelling against a construction in turn. */
    private <T> T introducingAlong(Core from, List<Core.FieldProjection.Step> steps, int next,
                                   BindingEnvironment names, OfAConstruction<T> found) {
        if (next == steps.size()) {
            return introducing(from, names, found);
        }
        return introducing(from, names, (construct, at) -> introducingAlong(
                given(construct, steps.get(next).field()), steps, next + 1, at, found));
    }

    /**
     * Where an element of any of {@code containers} stands.
     *
     * <p>The binding takes an element of a different one on each run, so where it stands is where
     * an element of each of them stands, taken together ({@link PathResolution#anyOf}). A container
     * standing at no position of the input leaves the runs through it saying nothing and takes
     * nothing away from the runs through the others: a block handed to a walk over the input and to
     * a walk over a list written in the body states the caller's rule about the input on the first
     * run whatever the second does.
     */
    private PathResolution oneOfTheElementsOf(BindingId binding, List<HeldIn> containers,
                                              BindingEnvironment names) {
        List<PathResolution> each = new ArrayList<>();
        for (HeldIn held : containers) {
            each.add(at(binding, held, names));
        }
        return PathResolution.anyOf(each);
    }

    private PathResolution elementOf(BindingId binding, BindingEnvironment names) {
        if (!(names.roleOf(binding) instanceof BindingRole.Element(var held))) {
            return new PathResolution.NotAPosition();
        }
        return at(binding, held, names);
    }

    /**
     * Where the part {@code held} names of its container stands.
     *
     * <p>The container names no position of this behavior's input — it is what another operation
     * answered, or something this does not read — so neither does anything it holds. Where a reading
     * of provenance goes on from there is not this walk's.
     */
    private PathResolution at(BindingId binding, HeldIn held, BindingEnvironment names) {
        return trail.through(binding,
                () -> heldAt(held.container(), new Wanted.APart(held.part()), names));
    }

    /**
     * Where a place of the pair a name read out of holds stands — a key or a value, where the pair
     * is an entry of a map.
     *
     * <p>An element a walk was handed may be a pair, and a pair is no position: it is two values
     * written together. What it is a pair of is the container's to say, and where the container is a
     * list of a map's entries, the first place of each is a key of that map and the second the value
     * filed under it. Any other pair says nothing about where its places stand.
     */
    private PathResolution placeOf(Core.TupleGet get, BindingEnvironment names) {
        if (!(Core.withoutStanding(get.tuple()) instanceof Core.Read r)) {
            return new PathResolution.NotAPosition();
        }
        Wanted place = new Wanted.APlaceOfAnElement(get.index());
        return switch (names.roleOf(r.binding())) {
            case BindingRole.Element(var held) -> held.part() != HeldIn.Part.ELEMENT
                    ? new PathResolution.NotAPosition()
                    : trail.through(r.binding(), () -> heldAt(held.container(), place, names));
            case BindingRole.ElementOfSeveral(var held) -> {
                List<PathResolution> each = new ArrayList<>();
                for (HeldIn one : held) {
                    if (one.part() == HeldIn.Part.ELEMENT) {
                        each.add(trail.through(r.binding(),
                                () -> heldAt(one.container(), place, names)));
                    }
                }
                yield PathResolution.anyOf(each);
            }
            case BindingRole.Alias(var value) -> trail.through(r.binding(),
                    () -> placeOf(new Core.TupleGet(value, get.index(), get.arity(), get.type(),
                            get.pos()), names));
            case BindingRole.Root _, BindingRole.Unknown _ -> new PathResolution.NotAPosition();
        };
    }

    /**
     * What of a container a walk is after.
     *
     * <p>A part of what it holds — its elements, or a map's keys — or one place of the pair each of
     * its elements is. Which it is decides what an operation between the container and the input
     * passes on: a list of a map's keys holds those keys as its elements, and a list of its entries
     * holds them at the first place of its elements.
     */
    private sealed interface Wanted {

        /** What the container holds, or the keys a map files it under. */
        record APart(HeldIn.Part part) implements Wanted {}

        /** The place at {@code index} of the pair each element of the container is. */
        record APlaceOfAnElement(int index) implements Wanted {}
    }

    /**
     * Where {@code wanted} of what {@code e} holds stands, and that it stands nowhere where it does.
     *
     * <p>Beside {@link #named} and not the same question. That one answers what an expression names,
     * and an operation's answer names no position — {@code List.reverse(xs)} is a value, not a place
     * a row writes at. What is asked here is where what that value holds is, and the library says: a
     * {@code reverse} answers the elements it was given and a {@code filter} some of them, so an
     * element of either is an element of what went in.
     *
     * <p>Only where they are the same values. Where an answer holds what a closure made of an
     * element, what it holds came from a position and is not one — and a line drawn there would be
     * at a position whose values are not the ones the rule is about, which an author cannot tell
     * from a line their model states.
     */
    private PathResolution heldAt(Core e, Wanted wanted, BindingEnvironment names) {
        PathResolution where = whereTaken(e, wanted);
        if (where != null) {
            return where;
        }
        // And where the expression names no position, what it holds may still be at one, so the
        // ways an operation's answer holds it are tried beside it.
        return switch (named(e, names)) {
            // A container at a position holds its parts under it. What an input's container holds
            // is never a pair, since a pair has no form a boundary writes, so a place of one names
            // nothing there.
            case PathResolution.At at -> switch (wanted) {
                // A container the elements reached it in another direction than the question asks
                // is a container of the same elements and not the order asked after.
                case Wanted.APart _ when asked == ElementQuestion.IN_THE_ORDER_WRITTEN
                        && walking != arrivingAs -> new PathResolution.NotAPosition();
                case Wanted.APart(var part) -> asksEveryOccurrence()
                        && at.path().insideAContainer()
                        ? new PathResolution.NotAPosition() : at.deeper(part::of);
                case Wanted.APlaceOfAnElement _ -> new PathResolution.NotAPosition();
            };
            // Each is a way to the same place, and neither is asked unless the other came back
            // without it, so whichever reached a position is the answer.
            case PathResolution.NotAPosition _ -> through(e, wanted, names);
            // A container standing at one of several places holds its parts at each of them. Read
            // further for one of them, what it holds would come back at a single place while the
            // container stands at more.
            case PathResolution.MayStandAt among -> switch (wanted) {
                case Wanted.APart(var part) -> asksEveryOccurrence()
                        ? new PathResolution.NotAPosition() : among.deeper(part::of);
                case Wanted.APlaceOfAnElement _ -> new PathResolution.NotAPosition();
            };
        };
    }

    /**
     * The ways an operation's answer holds what {@code wanted} names of what it was given, and no
     * position where the expression is not one of them.
     *
     * <p>Where an answer's elements came from, which keys it is filed under, and which part of a
     * map it lists are three facts about an operation, and each kind of thing wanted is followed by
     * the one that is about it.
     */
    private PathResolution through(Core standing, Wanted wanted, BindingEnvironment names) {
        // Which elements a value holds does not turn on the type it stands as.
        Core e = Core.withoutStanding(standing);
        if (e instanceof Core.Read r) {
            // A place of an element is crossed where the elements are: the same elements are the
            // same pairs.
            HeldIn.Part edge = switch (wanted) {
                case Wanted.APart(var part) -> part;
                case Wanted.APlaceOfAnElement _ -> HeldIn.Part.ELEMENT;
            };
            return switch (names.stepFrom(r.binding(), asked, edge)) {
                // Through a binding an expansion wrote, where the operation it removed answered the
                // part asked about as it was given. The operation is gone from this tree, so what
                // says so was written where it still stood.
                case ElementStep.Through(var same) -> trail.through(r.binding(),
                        () -> heldAt(new Core.Read(r.name(), same, r.type(), r.pos()), wanted,
                                names));
                // The question this walk is asking does not cross what was written here, which is
                // an answer and not a road not taken. What the binding holds is what the walk on
                // the other side of that edge made, so reading it is the crossing said another way.
                case ElementStep.Refused _ -> new PathResolution.NotAPosition();
                // And where nothing says where these elements came from, what the binding holds is
                // all there is. Looked up over the whole body and not down the path to here: a
                // container built by one operation and handed to the next is bound beside the
                // closure that reads it rather than above it.
                case ElementStep.NoEdge _ -> {
                    Core held = names.heldAnywhereBy(r.binding());
                    yield held == null ? new PathResolution.NotAPosition()
                            : trail.through(r.binding(), () -> heldAt(held, wanted, names));
                }
            };
        }
        // What a binding's body answers is read with the binding in scope, as a body a call was
        // expanded into binds its parameters around what it answers.
        if (e instanceof Core.LetIn let) {
            return heldAt(let.body(), wanted, names.inside(let.binder(), let.value()));
        }
        // A container chosen by cases holds, on each run, what the one the case taken answers
        // holds. How the cases come together is the question's.
        List<Core> arms = switch (e) {
            case Core.If iff -> List.of(iff.then(), iff.els());
            case Core.Match match -> match.cases().stream().map(Core.Case::body).toList();
            default -> null;
        };
        if (arms != null) {
            List<PathResolution> each = new ArrayList<>();
            for (Core arm : arms) {
                // Where a value stands or came from, a list written empty holds none for it to
                // be; every occurrence of a position is held on every run or by none.
                boolean holdsNone = Core.withoutStanding(arm) instanceof Core.ListLit written
                        && written.elements().isEmpty();
                if (!holdsNone || asksEveryOccurrence()) {
                    each.add(heldAt(arm, wanted, names));
                }
            }
            return switch (asked) {
                case NAMED_POSITION, VALUE_ORIGIN -> PathResolution.anyOf(each);
                case EVERY_OCCURRENCE, IN_THE_ORDER_WRITTEN -> PathResolution.inEveryCase(each);
                case ONE_PER_ELEMENT, SAME_EMPTINESS -> throw unaskedHere();
            };
        }
        // What an operation does to the order of what it was given is said of the ones declared
        // to turn it round, and of none other: a walk after the order stops at every other one,
        // even one answering each element as it is.
        if (asked == ElementQuestion.IN_THE_ORDER_WRITTEN) {
            return throughAnOperationTurningTheOrderRound(e, wanted, names);
        }
        // Or through an operation that answers what it was given, in either of the two shapes a
        // representation gives an application: the call a name reached where the operation has been
        // expanded away, and the operation standing as itself where it has not. What the library
        // says its answer holds is said of the operation, so it is asked once of that.
        ValueName operation;
        List<Core> args;
        switch (e) {
            case Core.Call call when call.fn() instanceof Core.Reached reached -> {
                operation = reached.denotes();
                args = call.args();
            }
            case Core.PreservedCall kept -> {
                operation = kept.declared().operation();
                args = kept.args();
            }
            default -> {
                return new PathResolution.NotAPosition();
            }
        }
        Crossing crossing = crossing(operation, wanted);
        if (crossing == null) {
            crossing = throughAnIdentityMap(operation, args, wanted, names);
        }
        if (crossing == null) {
            PathResolution flattened = throughAFlattening(operation, args, wanted, names);
            return flattened != null ? flattened : new PathResolution.NotAPosition();
        }
        // The call may be the runnable tree's and not a kept one, so its argument count is checked
        // here rather than by a kept call's own constructor.
        int argument = CallArguments.positionOf(crossing.argument(), operation);
        return argument < 0 || argument >= args.size() ? new PathResolution.NotAPosition()
                : heldAt(args.get(argument), crossing.wanted(), names);
    }

    /**
     * Where the elements of {@code e} stand when it is a call of an operation declared to answer
     * the elements of one argument in the opposite order: where they stand in that argument, handed
     * the other way round. Not a position where it is any other expression.
     */
    private PathResolution throughAnOperationTurningTheOrderRound(Core standing, Wanted wanted,
                                                                  BindingEnvironment names) {
        ValueName operation;
        List<Core> args;
        switch (Core.withoutStanding(standing)) {
            case Core.Call call when call.fn() instanceof Core.Reached reached -> {
                operation = reached.denotes();
                args = call.args();
            }
            case Core.PreservedCall kept -> {
                operation = kept.declared().operation();
                args = kept.args();
            }
            default -> {
                return new PathResolution.NotAPosition();
            }
        }
        int reversed = DefaultBoundOperationFacts.positionOfTheArgumentReversed(operation);
        if (reversed < 0 || reversed >= args.size()) {
            return new PathResolution.NotAPosition();
        }
        TraversalDirection outside = walking;
        walking = walking.reversed();
        try {
            return heldAt(args.get(reversed), wanted, names);
        } finally {
            walking = outside;
        }
    }

    /** Which argument of an operation what is wanted of its answer is found in, and what of that
     *  argument it is. */
    private record Crossing(DeclaredArgument argument, Wanted wanted) {}

    /**
     * The crossing of an operation answering what a closure made of each element, where the closure
     * made nothing of it ({@link AnIdentityMap}): the elements of the answer are the elements of the
     * argument, and a place of one is a place of the other. Null where it is any other operation, or
     * where what is wanted is no element of the answer.
     */
    private Crossing throughAnIdentityMap(ValueName operation, List<Core> args, Wanted wanted,
                                          BindingEnvironment names) {
        boolean ofAnElement = switch (wanted) {
            case Wanted.APart(HeldIn.Part part) -> part == HeldIn.Part.ELEMENT;
            case Wanted.APlaceOfAnElement _ -> true;
        };
        DeclaredArgument same = ofAnElement ? AnIdentityMap.of(operation, args,
                InputPath::blockStanding, names.heldByTheBody(), newtypes) : null;
        return same == null ? null : new Crossing(same, wanted);
    }

    /**
     * Where the elements of what {@code operation} answers stand, where it puts end to end the lists
     * its closure answered of each element of a container, and the closure answers a place of the
     * element ({@link PieceOfAnElement#WHAT_THE_CLOSURE_ANSWERS}) — or null where
     * it is any other operation or closure.
     *
     * <p>Each element of the answer is the value at that place of an element of the container, so
     * it stands inside the container's elements at the place and one container further in. The
     * container's elements are asked of the question in hand: where this walk wants every
     * occurrence, so does it of the container, and the answer is every occurrence of a position
     * with the container's containers and one more.
     */
    private PathResolution throughAFlattening(ValueName operation, List<Core> args, Wanted wanted,
                                              BindingEnvironment names) {
        if (!(wanted instanceof Wanted.APart(HeldIn.Part part)) || part != HeldIn.Part.ELEMENT) {
            return null;
        }
        BoundOperationFacts.Assembled assembled =
                DefaultBoundOperationFacts.get().assembles(operation);
        if (assembled == null
                || assembled.piece() != PieceOfAnElement.WHAT_THE_CLOSURE_ANSWERS) {
            return null;
        }
        int at = CallArguments.positionOf(assembled.source(), operation);
        Core.Block closure = at < 0 || at >= args.size() ? null
                : AnIdentityMap.closureBeside(args, at, InputPath::blockStanding);
        if (closure == null || closure.params().size() != 1
                || closure.params().getFirst().binding() == null) {
            return null;
        }
        ElementProjection answered = ElementProjection.read(closure.body(),
                closure.params().getFirst().binding(), names.heldByTheBody(), newtypes);
        if (answered == null) {
            return null;
        }
        PathResolution within = heldAt(args.get(at), wanted, names);
        return within instanceof PathResolution.NotAPosition ? null
                : within.deeper(base -> answered.from(base).element());
    }

    private static Core.Block blockStanding(Core closure) {
        return Core.withoutStanding(closure) instanceof Core.Block block ? block : null;
    }

    /**
     * Where {@code wanted} of what {@code operation} answers comes from, or null where the
     * operation says it comes from no argument.
     *
     * <p>Exhaustive over what can be wanted and over the parts of a map a list may hold, with no
     * {@code default}: each pair is the operation's fact read for one question, and a kind added to
     * either is a pair this has to answer.
     */
    private Crossing crossing(ValueName operation, Wanted wanted) {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        BoundOperationFacts.Listed listed = facts.listsAPartOf(operation);
        return switch (wanted) {
            // An element of a list of a map's keys or values is a key or a value of the map; an
            // element of a list of its entries is a pair, at no one position.
            case Wanted.APart(HeldIn.Part part) when part == HeldIn.Part.ELEMENT && listed != null ->
                    switch (listed.part()) {
                        case KEYS -> new Crossing(listed.map(), new Wanted.APart(HeldIn.Part.KEY));
                        case VALUES ->
                                new Crossing(listed.map(), new Wanted.APart(HeldIn.Part.ELEMENT));
                        case ENTRIES -> null;
                    };
            case Wanted.APart(HeldIn.Part part) when part == HeldIn.Part.ELEMENT -> {
                DeclaredArgument holds = holdingTheElements(operation);
                yield holds == null ? null : new Crossing(holds, wanted);
            }
            // A key is the same key in the answer only where the operation keeps the keys of a
            // map it was given, which is its own fact: an answer holding a map's very values may
            // hold them under other keys, and one whose values a closure rewrote keeps every key.
            case Wanted.APart _ -> {
                DeclaredArgument kept = facts.keepsTheKeysOf(operation);
                yield kept == null ? null : new Crossing(kept, wanted);
            }
            // The first place of an entry is its key and the second the value filed under it.
            case Wanted.APlaceOfAnElement(int index) when listed != null ->
                    listed.part() != MapPart.ENTRIES || index < 0 || index > 1 ? null
                            : new Crossing(listed.map(), new Wanted.APart(
                                    index == 0 ? HeldIn.Part.KEY : HeldIn.Part.ELEMENT));
            // The same elements are the same pairs, so a place of one is a place of the other.
            case Wanted.APlaceOfAnElement _ -> {
                DeclaredArgument holds = holdingTheElements(operation);
                yield holds == null ? null : new Crossing(holds, wanted);
            }
        };
    }

    /**
     * The argument whose very elements {@code operation}'s answer holds, or null where it holds no
     * argument's.
     *
     * <p>The one statement of it, for every walk that crosses an operation to the value it was
     * given: where a position stands and where a dependency's answer does are asked of the same
     * fact, so an element of a reordered or filtered list is an element of the list it came from
     * whichever of the two that list is.
     */
    static DeclaredArgument argumentWhoseElementsItHolds(ValueName operation) {
        BuiltFrom<DeclaredArgument> built =
                DefaultBoundOperationFacts.get().buildsItsResultFrom(operation);
        DeclaredArgument holds = built == null ? null : built.holdsTheElementsOf();
        // A set of a list's values holds the very values the list does, though not as often.
        if (holds == null && DefaultBoundOperationFacts.get().holdsTheImageOfEveryElement(operation)
                instanceof ElementLineage.SameAs<DeclaredArgument> same) {
            holds = same.source().argument();
        }
        return holds;
    }

    /**
     * The argument whose every element {@code operation}, applied to {@code args}, answers, each as
     * often, or null where it answers every element of none: the argument it puts in another
     * order, or the one a closure that answers each element as it is was handed.
     *
     * <p>The statement of what the walk after every occurrence of a position crosses at one
     * operation, for a walk that ends at an answer and not at a position.
     *
     * @param blockOf the block a closure argument stands for, or null where it stands for none
     * @param held    what each binding of the body holds
     */
    static DeclaredArgument argumentKeepingEveryElement(ValueName operation, List<Core> args,
                                                        Function<Core, Core.Block> blockOf,
                                                        Map<BindingId, Core> held,
                                                        DeclarationNewtypes newtypes) {
        BuiltFrom<DeclaredArgument> built =
                DefaultBoundOperationFacts.get().buildsItsResultFrom(operation);
        DeclaredArgument permuted = built == null ? null : built.permutesTheElementsOf();
        return permuted != null ? permuted
                : AnIdentityMap.of(operation, args, blockOf, held, newtypes);
    }

    /** The argument whose elements {@code operation}'s answer holds, as far as this walk's question
     *  crosses, or null where it crosses to none. */
    private DeclaredArgument holdingTheElements(ValueName operation) {
        BuiltFrom<DeclaredArgument> built =
                DefaultBoundOperationFacts.get().buildsItsResultFrom(operation);
        // Each as often is more than the same values: an answer that keeps some of what it was
        // given holds those and not the rest.
        switch (asked) {
            case EVERY_OCCURRENCE -> {
                return built == null ? null : built.permutesTheElementsOf();
            }
            // Answered in `through` by the operations that turn the order round, and stopped there
            // at every other before it is asked of.
            case IN_THE_ORDER_WRITTEN -> throw new IllegalStateException("a walk after the order"
                    + " asks no operation of what it holds, and " + operation + " was asked of");
            case NAMED_POSITION, VALUE_ORIGIN, ONE_PER_ELEMENT, SAME_EMPTINESS -> { }
        }
        DeclaredArgument holds = argumentWhoseElementsItHolds(operation);
        // What is made from a position came from it and is not it, so an answer holding only that
        // is crossed by the walk after where a value came from and not by the walk after which
        // position an expression names — the same two licences an edge written by an expansion
        // carries ({@link souther.compiler.check.ElementProvenance#stepFrom}), read here from the
        // declaration that states them because the operation is still standing to be asked.
        return holds != null ? holds
                : switch (asked) {
                    case VALUE_ORIGIN -> built != null ? built.derivesItsElementsFrom()
                            : DefaultBoundOperationFacts.get().elementsMadeFromAlone(operation);
                    case NAMED_POSITION, EVERY_OCCURRENCE, IN_THE_ORDER_WRITTEN -> null;
                    case ONE_PER_ELEMENT, SAME_EMPTINESS -> throw unaskedHere();
                };
    }

    /** A walk after a position was handed a question about one value for each element, which is
     *  answered a step at a time ({@link #oneStepBeneath}) and never by this walk. */
    private IllegalStateException unaskedHere() {
        return new IllegalStateException("a walk after a position was asked " + asked
                + ", which is answered a step at a time beneath a list");
    }

    /**
     * One step from a list to the list it was made from, for a walk asking {@code question}: the
     * list one step beneath, and what the step answered of each of that list's elements — or null
     * where the list was made by nothing this question crosses.
     *
     * @param from     the list beneath
     * @param answered what the list holds for each element of {@code from}, where the question asks
     *                 it ({@link ElementQuestion#ONE_PER_ELEMENT}); null where it does not
     */
    record Beneath(Core from, OnePerElement.Answered answered) {}

    /**
     * Whether a walk asking {@code question} goes on with the list {@code asked}, which following
     * the names it stands for came to {@code reached}.
     *
     * <p>A question about one value for each element counts which of the values are equal, and
     * what one type calls equal is not shown to be what another does. So the list must be of one
     * type as it was asked and as it was reached, and stand as no wider type at either: following
     * names is free to set aside the type a value stood as on the way, and a type kept from the
     * one to the other is what this walk can show of it — a condition it asks, and no record that
     * nothing was set aside. Whether a list holds something does not turn on the type it stands
     * as, so that question asks none of this.
     *
     * <p>Asked before anything else is of what was reached, a position it names among them: a list
     * that names one, reached from a list of another type, has held nothing yet the question can
     * use.
     */
    static boolean goesOnThrough(Core asked, Core reached, ElementQuestion question) {
        return switch (question) {
            case ONE_PER_ELEMENT -> !(asked instanceof Core.Widen)
                    && !(reached instanceof Core.Widen) && asked.type().equals(reached.type());
            case SAME_EMPTINESS -> true;
            case NAMED_POSITION, VALUE_ORIGIN, EVERY_OCCURRENCE, IN_THE_ORDER_WRITTEN ->
                    throw new IllegalArgumentException("a list is followed beneath for a question"
                            + " about one value for each element, not " + question);
        };
    }

    /**
     * The step beneath {@code list} a walk asking {@code question} takes, where the list is the
     * answer of an operation the walk crosses or a binding an expansion said holds another's
     * elements — or null where it takes none.
     *
     * <p>The one statement of what each of the two questions about one value for each element
     * crosses. An operation that puts the elements in another order holds each of them once, so
     * both cross it. An operation answering one value for each element holds something exactly
     * where its argument does, so the walk after holding something crosses it whatever the closure
     * answers; the walk after one value for each element crosses it only where the closure answers
     * a place of the element, or a newtype wearing one ({@link OnePerElement.Answered}). An
     * operation keeping some of the elements, or answering several for one, is crossed by neither.
     * What an expansion wrote of a binding's elements is read for the question
     * ({@link souther.compiler.check.ElementProvenance#stepFrom}).
     *
     * <p>A step and not the walk: what a name stands for, and what a parameter of a body entered is
     * handed, is the reading's to say, and the reading takes the step from where the list stands.
     *
     * @param blockOf the block a closure argument stands for, where the call stands
     */
    static Beneath oneStepBeneath(Core list, ElementQuestion question, BindingEnvironment names,
                                  DeclarationNewtypes newtypes,
                                  Function<Core, Core.Block> blockOf) {
        boolean asksWhatEachIs = switch (question) {
            case ONE_PER_ELEMENT -> true;
            case SAME_EMPTINESS -> false;
            case NAMED_POSITION, VALUE_ORIGIN, EVERY_OCCURRENCE, IN_THE_ORDER_WRITTEN ->
                    throw new IllegalArgumentException("a step beneath a list is taken for a"
                            + " question about one value for each element, not " + question);
        };
        // What a step that hands the elements on as they are answered of each, where it is asked.
        OnePerElement.Answered asTheyAre = asksWhatEachIs ? OnePerElement.Answered.ITSELF : null;
        if (!goesOnThrough(list, list, question)) {
            return null;
        }
        Core e = Core.withoutStanding(list);
        if (e instanceof Core.Read r) {
            return switch (names.stepFrom(r.binding(), question, HeldIn.Part.ELEMENT)) {
                case ElementStep.Through(var same) -> new Beneath(
                        new Core.Read(r.name(), same, r.type(), r.pos()), asTheyAre);
                // What was made from the elements, or some of them, is not them each once.
                case ElementStep.Refused _ -> null;
                // Where nothing says where the elements came from, what the binding holds is all
                // there is, looked up over the whole body as the walk after a position does: a
                // container built by one operation and handed to the next is bound beside the
                // closure that reads it rather than above it.
                case ElementStep.NoEdge _ -> {
                    Core held = names.heldAnywhereBy(r.binding());
                    yield held == null ? null : new Beneath(held, asTheyAre);
                }
            };
        }
        ValueName operation;
        List<Core> args;
        switch (e) {
            case Core.Call call when call.fn() instanceof Core.Reached reached -> {
                operation = reached.denotes();
                args = call.args();
            }
            case Core.PreservedCall kept -> {
                operation = kept.declared().operation();
                args = kept.args();
            }
            default -> {
                return null;
            }
        }
        // A set made a list holds each of its elements once, which no fact about what an
        // operation builds says of a set; an operation that puts a list's in another order is
        // listed so as well.
        int listed = DefaultBoundOperationFacts.positionOfTheArgumentListedOnce(operation);
        if (listed >= 0 && listed < args.size()) {
            return new Beneath(args.get(listed), asTheyAre);
        }
        BuiltFrom<DeclaredArgument> built =
                DefaultBoundOperationFacts.get().buildsItsResultFrom(operation);
        if (built == null) {
            return null;
        }
        int permuted = built.permutesTheElementsOf() == null ? -1
                : CallArguments.positionOf(built.permutesTheElementsOf(), operation);
        if (permuted >= 0 && permuted < args.size()) {
            return new Beneath(args.get(permuted), asTheyAre);
        }
        int mapped = built.mapsEachElementOf() == null ? -1
                : CallArguments.positionOf(built.mapsEachElementOf(), operation);
        Core.Block closure = mapped < 0 || mapped >= args.size() ? null
                : AnIdentityMap.closureBeside(args, mapped, blockOf);
        if (closure == null || closure.params().size() != 1
                || closure.params().getFirst().binding() == null) {
            return null;
        }
        if (!asksWhatEachIs) {
            return new Beneath(args.get(mapped), null);
        }
        OnePerElement.Answered answered = OnePerElement.Answered.of(closure.body(),
                closure.params().getFirst().binding(), names.heldByTheBody(), newtypes);
        return answered == null ? null : new Beneath(args.get(mapped), answered);
    }
}
