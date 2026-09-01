package souther.compiler.inputs;

import souther.compiler.check.CallArguments;
import souther.compiler.check.Location;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.types.BindingId;

/**
 * Which position of a behavior's input an expression names, where it names none, or where this did
 * not read far enough to say ({@link PathResolution}).
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
 * <p>Which is about what stops the steps and not about how many shapes are taken. Not every shape
 * is descended — an expression that binds a name of its own is one this does not go under, and it
 * comes back said rather than answered ({@link PathResolution.Reason}).
 *
 * <p>What is known of the names comes in as facts and nothing else ({@link BindingEnvironment}).
 * How many of them there are is not a fact about how far a value's provenance runs — a name bound in
 * an arm is read under bindings written elsewhere — and a reading of what a name means is built on
 * this one rather than beside it, so neither is something a walk here can reach for.
 *
 * <p>Nothing about the reading of an input reaches this and nothing here reaches it: what a position
 * can hold is read from the declarations ({@link InputDomain}), and this only says which position an
 * expression is pointing at.
 */
final class InputPath {

    private final Symbols symbols;
    private final ElementQuestion asked;
    private final BindingTrail trail = new BindingTrail();

    private InputPath(Symbols symbols, ElementQuestion asked) {
        this.symbols = symbols;
        this.asked = asked;
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
    static PathResolution of(Core e, BindingEnvironment names, Symbols symbols) {
        return new InputPath(symbols, ElementQuestion.NAMED_POSITION).named(e, names);
    }

    /**
     * Where {@code e}'s value came from, and that it came from none where it did.
     *
     * <p>Beside {@link #of} and licensing less. That one answers which position an expression names,
     * and what a row writes at a position is what a rule about it is about; this answers where a
     * value came from, and a value made from a position is not that position — a rule about it is
     * not a rule about the values there, and nothing here says what it comes to for them.
     *
     * <p>So what this is for is saying that a rule was written. An author who filters what a
     * {@code map} answered wrote a comparison, and a reading that could place it nowhere said
     * nothing at all — which reads as a model with no rule there rather than a rule this could not
     * follow.
     */
    static PathResolution cameFrom(Core e, BindingEnvironment names, Symbols symbols) {
        return new InputPath(symbols, ElementQuestion.VALUE_ORIGIN).named(e, names);
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
                                    Symbols symbols) {
        return new InputPath(symbols, ElementQuestion.NAMED_POSITION).elementOf(binding, names);
    }

    private PathResolution named(Core e, BindingEnvironment names) {
        return switch (e) {
            case Core.Read r -> {
                TermPath stands = names.rootOf(r.binding());
                if (stands != null) {
                    yield new PathResolution.At(stands);
                }
                // Three ways a name reaches a position and no more. It is a parameter; or it holds
                // what something else was, which is followed; or an operation of the language handed
                // it an element of a container, and then it is at the container's position, inside
                // it. The third is the one no walk over the tree that runs could work out — what
                // handed it is gone by then — and it is read from what was recorded where the
                // operation still stood.
                Core held = names.boundValueOf(r.binding());
                PathResolution holds = held == null ? new PathResolution.NotAPosition()
                        : trail.through(r.binding(), () -> named(held, names));
                if (holds instanceof PathResolution.At) {
                    yield holds;
                }
                // What it holds names no position, and it may still be an element of one. Two
                // walks over one collection joined into one leave a binding that is both: it
                // holds what the first walk made, and it is what the second was handed. Stopping
                // at the first left every rule inside the second reading as being about nothing.
                yield either(holds, elementOf(r.binding(), names));
            }
            case Core.FieldAccess fa -> switch (named(fa.target(), names)) {
                case PathResolution.At(var base) -> new PathResolution.At(
                        Location.isStep(fa.target().type(), fa.field(), symbols)
                                ? base.then(fa.field()) : base);
                case PathResolution other -> other;
            };
            // A name bound inside the expression handed over, which this reading does not go under.
            // What it comes to is what its body comes to under that name, and whether the name may
            // stand for the position its value names is a question about the model rather than
            // about the shape — so what is said is that this was not read.
            case Core.LetIn _ -> new PathResolution.Unread(
                    PathResolution.Reason.A_NAME_BOUND_INSIDE_THE_EXPRESSION);
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
            case null, default -> new PathResolution.NotAPosition();
        };
    }

    private PathResolution elementOf(BindingId binding, BindingEnvironment names) {
        Core container = names.containerOf(binding);
        if (container == null) {
            return new PathResolution.NotAPosition();
        }
        // The container names no position of this behavior's input — it is what another operation
        // answered, or something this does not read — so neither does an element of it. Where a
        // reading of provenance goes on from there is not this walk's.
        return switch (trail.through(binding, () -> containerPath(container, names))) {
            case PathResolution.At(var at) -> new PathResolution.At(at.element());
            case PathResolution other -> other;
        };
    }

    /**
     * Which position holds the elements {@code e} holds, and that none does where none does.
     *
     * <p>Beside {@link #named} and not the same question. That one answers what an expression names,
     * and an operation's answer names no position — {@code List.reverse(xs)} is a value, not a place
     * a row writes at. What is asked here is where the elements of that value are, and the library
     * says: a {@code reverse} answers the elements it was given and a {@code filter} some of them,
     * so an element of either is an element of what went in.
     *
     * <p>Only where they are the same values. Where an answer holds what a closure made of an
     * element, what it holds came from a position and is not one — and a line drawn there would be
     * at a position whose values are not the ones the rule is about, which an author cannot tell
     * from a line their model states.
     */
    private PathResolution containerPath(Core e, BindingEnvironment names) {
        PathResolution named = named(e, names);
        if (named instanceof PathResolution.At) {
            return named;
        }
        // And where the expression names no position, its elements may still be at one, so the ways
        // an operation's answer holds them are tried beside it.
        return either(named, elementsOf(e, names));
    }

    /**
     * The answer of two readings of one expression.
     *
     * <p>A position wherever either reached one, since each is a way to the same place and neither
     * is asked unless the other came back without it. Where neither did, what this compiler did not
     * read stands over what the model does not hold: one of the two says the answer is not known
     * here, and an absence that has that in it is not an absence.
     *
     * <p>The one place the three are ordered. Written at each meeting of two readings instead, the
     * orderings drift apart, and the one that forgets turns a reading that stopped into a model
     * that states nothing — which is the whole of what this type is for.
     */
    private static PathResolution either(PathResolution one, PathResolution other) {
        return switch (one) {
            case PathResolution.At _ -> one;
            case PathResolution.Unread _ -> switch (other) {
                case PathResolution.At _ -> other;
                case PathResolution.NotAPosition _, PathResolution.Unread _ -> one;
            };
            case PathResolution.NotAPosition _ -> switch (other) {
                case PathResolution.At _, PathResolution.NotAPosition _,
                     PathResolution.Unread _ -> other;
            };
        };
    }

    /** The ways an operation's answer holds the elements of what it was given, and no position
     *  where the expression is not one of them. */
    private PathResolution elementsOf(Core e, BindingEnvironment names) {
        if (e instanceof Core.Read r) {
            // Through a binding an expansion wrote, where the operation it removed answered the
            // elements it was given. The operation is gone from this tree, so what says so was
            // written where it still stood.
            BindingId same = names.predecessorOf(r.binding(), asked);
            if (same != null) {
                return trail.through(r.binding(), () -> containerPath(
                        new Core.Read(r.name(), same, r.type(), r.pos()), names));
            }
            // Or through what the binding holds. Looked up over the whole body and not down the
            // path to here: a container built by one operation and handed to the next is bound
            // beside the closure that reads it rather than above it.
            Core held = names.heldAnywhereBy(r.binding());
            return held == null ? new PathResolution.NotAPosition()
                    : trail.through(r.binding(), () -> containerPath(held, names));
        }
        // Or through an operation the language keeps standing that answers what it was given.
        if (!(e instanceof Core.Call call) || !(call.fn() instanceof Core.Reached reached)) {
            return new PathResolution.NotAPosition();
        }
        ArgumentRef holds = ElementLineage.holdsTheElementsOf(reached.denotes());
        int argument = holds == null ? -1 : CallArguments.positionIn(holds, reached.denotes());
        return argument < 0 || argument >= call.args().size() ? new PathResolution.NotAPosition()
                : containerPath(call.args().get(argument), names);
    }
}
