package souther.compiler.inputs;

import souther.compiler.semantics.ArgumentRef;

import souther.compiler.check.Location;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.Map;

/**
 * Which position of a behavior's input an expression names, or nothing where it names none.
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
 * <p>Nothing about the reading of an input reaches this and nothing here reaches it: what a position
 * can hold is read from the declarations ({@link InputDomain}), and this only says which position an
 * expression is pointing at.
 */
public final class InputPath {

    /**
     * The position {@code e} names.
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
     */
    public static TermPath of(Core e, InputDomain read, Symbols symbols) {
        return of(e, read.parameterReads(), Map.of(),
                souther.compiler.check.ElementBindings.NONE, symbols, false);
    }

    /**
     * The same, through what a run of {@code let}s bound on the way.
     *
     * <p>A name bound to an input position is that position: what a {@code let} binds is evaluated
     * on the way to the answer, so a body that names its argument and then matches the name is
     * matching the argument. That is what a helper expanded into a body looks like — the call's
     * argument bound to the helper's own parameter — and reading only the outermost name would
     * leave every claim inside an expanded helper about a position nothing here can name.
     *
     * <p>Only through what was bound, and only to a value that is itself a position. A binding whose
     * value is a call is a value the rules of no position say anything about, and it answers
     * nothing here.
     *
     * @param roots      which bindings name which parameter, in the tree being walked
     * @param bound      what each binding on the way holds, in the order they were passed
     * @param callsStand whether this tree is one that keeps the operations the language defines the
     *                   meaning of standing. Where it is, such a call names no location and that is
     *                   the answer; where it is not, meeting one says the walk was handed a
     *                   representation it does not read
     */
    public static TermPath of(Core e, Map<BindingId, String> roots, Map<BindingId, Core> bound,
                              souther.compiler.check.ElementBindings elements, Symbols symbols,
                              boolean callsStand) {
        return of(e, roots, bound, elements, symbols, callsStand, 0, false);
    }

    /**
     * The position {@code e}'s value came from, or null where it came from none.
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
    public static TermPath cameFrom(Core e, Map<BindingId, String> roots,
                                    Map<BindingId, Core> bound,
                                    souther.compiler.check.ElementBindings elements,
                                    Symbols symbols, boolean callsStand) {
        return of(e, roots, bound, elements, symbols, callsStand, 0, true);
    }

    /**
     * Which position holds the elements {@code container} holds, or null where none does.
     *
     * <p>Beside {@link #of} and not the same question. That one answers what an expression names,
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
    private static TermPath containerPath(Core e, Map<BindingId, String> roots,
                                          Map<BindingId, Core> bound,
                                          souther.compiler.check.ElementBindings elements,
                                          Symbols symbols, boolean callsStand, int through,
                                          boolean made) {
        TermPath named = of(e, roots, bound, elements, symbols, callsStand, through, made);
        if (named != null || through >= bound.size() + elements.containers().size() + FOLLOWED) {
            return named;
        }
        if (e instanceof Core.Read r) {
            // Through a binding an expansion wrote, where the operation it removed answered the
            // elements it was given. The operation is gone from this tree, so what says so was
            // written where it still stood.
            souther.compiler.types.BindingId same =
                    elements.provenance().sameElementsAs(r.binding());
            // And through one whose elements were made from another's, where what is being asked is
            // where a value came from. Never where the question is which position it is: a value
            // made from a position is not that position.
            if (same == null && made) {
                same = elements.provenance().madeFrom(r.binding());
            }
            if (same != null) {
                return containerPath(new Core.Read(r.name(), same, r.type(), r.pos()),
                        roots, bound, elements, symbols, callsStand, through + 1, made);
            }
            // Or through what the binding holds. Looked up over the whole body and not down the
            // path to here: a container built by one operation and handed to the next is bound
            // beside the closure that reads it rather than above it.
            Core held = bound.containsKey(r.binding()) ? bound.get(r.binding())
                    : elements.boundTo(r.binding());
            return held == null ? null
                    : containerPath(held, roots, bound, elements, symbols, callsStand,
                        through + 1, made);
        }
        // Or through an operation the language keeps standing that answers what it was given.
        if (!(e instanceof Core.Call call) || !(call.fn() instanceof Core.Reached reached)) {
            return null;
        }
        ArgumentRef holds =
                souther.compiler.semantics.ElementLineage.holdsTheElementsOf(reached.denotes());
        int argument = holds == null ? -1 : souther.compiler.check.CallArguments.positionIn(holds, reached.denotes());
        return argument < 0 || argument >= call.args().size() ? null
                : containerPath(call.args().get(argument), roots, bound, elements, symbols,
                        callsStand, through + 1, made);
    }

    /**
     * The position an element handed to {@code binding} stands at, or null where it stands at none.
     *
     * <p>What an operation of the language hands its closure is an element of the container it was
     * given, so the name it arrives under stands at that container's position, inside it. Asked of
     * the binding rather than of the container's expression: a container built by one operation and
     * handed to the next names no position of its own, and the elements are the same elements.
     */
    public static TermPath elementAt(BindingId binding, Map<BindingId, String> roots,
                                     Map<BindingId, Core> bound,
                                     souther.compiler.check.ElementBindings elements,
                                     Symbols symbols, boolean callsStand) {
        return elementOf(binding, roots, bound, elements, symbols, callsStand, 0, false);
    }

    private static TermPath elementOf(BindingId binding, Map<BindingId, String> roots,
                                      Map<BindingId, Core> bound,
                                      souther.compiler.check.ElementBindings elements,
                                      Symbols symbols, boolean callsStand, int through,
                                      boolean made) {
        Core container = elements.containerOf(binding);
        if (container == null) {
            return null;
        }
        TermPath at = containerPath(container, roots, bound, elements, symbols,
                callsStand, through + 1, made);
        // The container names no position of this behavior's input — it is what another operation
        // answered, or something this does not read — so neither does an element of it. Where a
        // reading of provenance goes on from there is not this walk's.
        return at == null ? null : at.element();
    }

    /** How many operations deep the elements of one container are followed. */
    private static final int FOLLOWED = 8;

    private static TermPath of(Core e, Map<BindingId, String> roots, Map<BindingId, Core> bound,
                               souther.compiler.check.ElementBindings elements, Symbols symbols,
                               boolean callsStand, int through, boolean made) {
        return switch (e) {
            case Core.Read r -> {
                String parameter = roots.get(r.binding());
                if (parameter != null) {
                    yield TermPath.of(parameter);
                }
                // Three ways a name reaches a position and no more. It is a parameter; or it holds
                // what something else was, which is followed; or an operation of the language handed
                // it an element of a container, and then it is at the container's position, inside
                // it. The third is the one no walk over the tree that runs could work out — what
                // handed it is gone by then — and it is read from what was recorded where the
                // operation still stood.
                Core held = bound.get(r.binding());
                // A binding holds one value, so following it cannot come back to itself; the count
                // is what says so to a reader rather than a claim in a comment.
                int steps = bound.size() + elements.containers().size();
                if (through >= steps) {
                    yield null;
                }
                if (held != null) {
                    TermPath through_ =
                            of(held, roots, bound, elements, symbols, callsStand, through + 1, made);
                    if (through_ != null) {
                        yield through_;
                    }
                    // What it holds names no position, and it may still be an element of one. Two
                    // walks over one collection joined into one leave a binding that is both: it
                    // holds what the first walk made, and it is what the second was handed. Stopping
                    // at the first left every rule inside the second reading as being about nothing.
                }
                yield elementOf(r.binding(), roots, bound, elements, symbols, callsStand,
                        through, made);
            }
            case Core.FieldAccess fa -> {
                TermPath base = of(fa.target(), roots, bound, elements, symbols, callsStand,
                        through, made);
                if (base == null) {
                    yield null;
                }
                yield Location.isStep(fa.target().type(), fa.field(), symbols)
                        ? base.then(fa.field()) : base;
            }
            // A call kept standing names no location. Where the walk is over a tree that keeps them
            // that is the answer, and where it is not, its presence says this walk was handed a
            // representation it does not read — said rather than answered with "no path", which
            // would be the same answer a number gives.
            case Core.PreservedCall p -> {
                if (!callsStand) {
                    throw p.unexpectedIn("an input position");
                }
                yield null;
            }
            case null, default -> null;
        };
    }

    private InputPath() {}
}
