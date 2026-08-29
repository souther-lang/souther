package souther.compiler.inputs;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What a tree's names stand for, in terms of a behavior's input, where the reader has got to.
 *
 * <p>A reader meets a position under whatever name is in scope there, and the name is not the
 * position. Three things make that so, and one value carries them.
 *
 * <p>A tree may bind a name the behavior already binds. {@code let order = withDefaults(order)}
 * leaves every read below it naming the local, whose values are whatever the call answers with — so
 * a reader matching the word says about the parameter's rules what is true of nothing.
 *
 * <p>And a body reaches a position through the names bound on the way to it. A helper expanded into
 * a body binds the call's argument to the helper's own parameter and matches that, so a reader that
 * followed no binding would find every statement inside an expanded helper about a position it
 * cannot name — which is most of what a model's rules are written in.
 *
 * <p>And the parameters themselves are bound more than once. An implementation binds them where its
 * body reads them; the declaration binds them where its own {@code ensures} clauses do. Which
 * position a name points at is the same question in either tree, and which bindings ask it is not —
 * so the roots belong to the reading rather than to the input, and a reading given the other one's
 * finds every comparison about nothing.
 *
 * <p>And a name stands for more than a position or nothing. It is a position, or the expression it
 * was given, or one of several values this can write out, or an element an operation handed out, or
 * something this knows nothing about ({@link ReadMeaning}). Answered as a position and nothing, the
 * last four were one answer, and a rule written over a name given arithmetic over positions was read
 * as no rule at all.
 *
 * <p>Nothing here decides what a position holds; that is the reading of the declarations
 * ({@link InputDomain}), and this only says what a name is pointing at.
 *
 * @param roots        which bindings name which parameter, in the tree being walked
 * @param alternatives which bindings stand for one of several values, and which values those are.
 *                     Written where an arm narrows what it was handed and read nowhere else: an
 *                     element's own alternatives are worked out from the container it came from, and
 *                     what an arm leaves of them is a fact about this walk's position in the tree
 *                     that nothing under the arm could recover
 * @param callsStand   whether an operation the language defines the meaning of is left standing in
 *                     this tree. It is in the representation a declaration's own rules are read in
 *                     and it is not in the one that runs, and the difference is not a detail of the
 *                     walk: a call left standing names no location, which is an answer where such a
 *                     tree is what was handed over and a bug in the caller where it is not
 */
public record InputReads(InputDomain read, Map<BindingId, TermPath> roots,
                         Map<BindingId, Core> bound,
                         souther.compiler.check.ElementBindings elements,
                         Map<BindingId, java.util.List<Denotation>> alternatives,
                         boolean callsStand)
        implements InputPaths {

    public InputReads {
        roots = Map.copyOf(roots);
        bound = Map.copyOf(bound);
        alternatives = Map.copyOf(alternatives);
    }

    /** At the top of a body, where nothing has been bound yet and no element has been handed out. */
    public static InputReads of(InputDomain read) {
        return of(read, souther.compiler.check.ElementBindings.NONE);
    }

    /**
     * At the top of a body, before there is a reading of the input to hold beside it.
     *
     * <p><b>What the paths a body names are worked out from, and it is not the reading.</b> Which
     * location a name stands for is settled by the parameters, the bindings on the way and the case
     * an arm selects — all of them facts about the tree. Whether a row is ever written at the
     * location is the reading's answer and is asked of the reading, about the path this produced.
     *
     * <p>Held apart because they cannot both be asked at once: the reading is built over the paths a
     * behavior's measurement names, so a path environment that consulted the reading could not be
     * used to find them. One built this way answers about names and refuses to answer about the
     * model, which is what keeps the two questions from being run together again.
     */
    public static InputReads ofParameters(Map<BindingId, String> parameters,
                                          souther.compiler.check.ElementBindings elements) {
        return new InputReads(null, rooted(parameters), Map.of(), elements, Map.of(), false);
    }

    /**
     * The reading of the input this was built beside.
     *
     * <p>Absent where this was built to find the paths a body names ({@link #ofParameters}), and
     * asking for it there is a caller reaching for an answer that does not exist yet rather than one
     * that happens to be missing.
     */
    public InputDomain read() {
        if (read == null) {
            throw new IllegalStateException(
                    "a path environment built before the reading was asked for the reading");
        }
        return read;
    }

    /**
     * The same, of a body whose operations handed their closures the contents of containers.
     *
     * <p>Read where those operations still stood and carried here, since the tree this walks has
     * none of them left in it. A reading given nothing finds every name inside a closure naming no
     * position, which is what it did before there was anything to give.
     */
    public static InputReads of(InputDomain read, souther.compiler.check.ElementBindings elements) {
        return new InputReads(read, rooted(read.parameterReads()), Map.of(), elements,
                Map.of(), false);
    }

    /** The parameters as positions, which is what a name in a tree stands for. */
    private static Map<BindingId, TermPath> rooted(Map<BindingId, String> named) {
        Map<BindingId, TermPath> out = new LinkedHashMap<>();
        named.forEach((binding, name) -> out.put(binding, TermPath.of(name)));
        return out;
    }

    /**
     * At the top of a rule the behavior itself declares, which meets the parameters under the
     * bindings the declaration gave them rather than the ones an implementation did.
     *
     * <p>Which is why this takes them rather than reading them off {@code read}: a behavior nothing
     * implements binds its parameters nowhere a body could, and its clauses still name them.
     */
    public static InputReads ofWhatIsDeclared(InputDomain read, Map<BindingId, String> roots) {
        return new InputReads(read, rooted(roots), Map.of(),
                souther.compiler.check.ElementBindings.NONE, Map.of(), true);
    }

    /**
     * The same, of a clause a declaration wrote about a value standing somewhere in the input.
     *
     * <p>Rooted at paths rather than at parameter names, which is what such a clause needs: it binds
     * the fields of the declaration that wrote it, and those fields stand wherever a value of that
     * declaration stands — under a parameter, under a field of one, under what a sequence holds. A
     * name here is a field's binding and never a parameter's, so there is no name to look a
     * parameter up by.
     *
     * <p>The operations the language defines the meaning of are left standing, as they are in every
     * reading of what a declaration wrote: that is the representation a declaration's own rules are
     * held in, and a clause read in the one that runs would have the calls in it gone.
     */
    public static InputReads ofADeclaredClause(InputDomain read, Map<BindingId, TermPath> roots) {
        return new InputReads(read, roots, Map.of(),
                souther.compiler.check.ElementBindings.NONE, Map.of(), true);
    }

    /** The same, before there is a reading to hold beside it ({@link #ofParameters}). */
    public static InputReads ofWhatIsDeclared(Map<BindingId, String> roots) {
        return new InputReads(null, rooted(roots), Map.of(),
                souther.compiler.check.ElementBindings.NONE, Map.of(), true);
    }

    /**
     * The same, inside one arm of a {@code match}.
     *
     * <p>A name an arm binds stands for the value that was matched, read as the case the arm
     * selects — which is the position the scrutinee is at, narrowed. Written here and nowhere else:
     * every walk that goes into an arm meets the same binder, and each working out for itself what
     * it names is as many spellings of one position as there are walks, of which the axes carry
     * one.
     *
     * <p>Only where the arm selects one case. An arm answering for several narrows to none of them
     * in particular, and a name that stands for no position is what a reader is given for it —
     * which is what it was given before there was anything to say.
     *
     * <p><b>And where the scrutinee stands for one of several written values, the arm narrows that
     * set.</b> Which is a different answer from the one above and not a weaker copy of it: a
     * position is one place a row writes at, and a set is every value the name can take. An arm
     * admitting one case takes out the members that are not of it and leaves the rest — however
     * many that is. A container written with two members of the admitted case leaves two, and an
     * arm is no evidence that the name is one of them: what would make it one is there being one
     * left, which is what the set says and the arm does not.
     */
    @Override
    public InputReads insideArm(Core.Match match, Core.Case arm, Symbols symbols) {
        if (arm.binder() == null || arm.binder().binding() == null) {
            return this;
        }
        if (arm.caseTypes().size() != 1) {
            return admitting(match, arm, symbols);
        }
        TermPath scrutinee = pathOf(match.scrutinee(), symbols);
        if (scrutinee == null) {
            return admitting(match, arm, symbols);
        }
        TermPath narrowed = scrutinee.refine(Refinement.sumCase(arm.caseTypes().get(0)));
        // And nothing is asked of the reading. What this answers is which location the arm's name
        // stands for, which the arm and the scrutinee's path settle between them: the value that was
        // matched, read as the case the arm selects. Whether a row is ever written there — whether
        // the position exists, whether the rules leave the case anything — is a question about the
        // model, and it is {@link InputDomain}'s to answer about the path this produced.
        //
        // Held together, the two could not both be answered: the reading has to be built before it
        // can be asked, and it cannot be built without knowing which paths the body names. Asking
        // only the first here is what breaks that circle, and the cost of asking it alone is a name
        // that stands for a place no row reaches — which the reading refuses when it is asked.
        Map<BindingId, TermPath> wider = new LinkedHashMap<>(roots);
        wider.put(arm.binder().binding(), narrowed);
        return new InputReads(read, wider, bound, elements, alternatives, callsStand);
    }

    /**
     * The same, where what the arm binds is one of the values the scrutinee's set holds.
     *
     * <p>Only where the arm's carriers are the values themselves. A case that binds what an optional
     * holds binds something under the value that was matched rather than the value, so the members
     * of the set are not what the name stands for — and a set narrowed as though they were would
     * name every member one step too high.
     *
     * <p>Nothing is narrowed where a member cannot be told which case it is. What makes the set an
     * answer is that it holds every value the name can take, and a filter that let through what it
     * could not classify would be keeping a member the arm excludes, while one that dropped it would
     * be losing a member the arm admits. Neither is the set, so the name is left with none.
     *
     * <p>Which a member is is read off the construction or the case written where it stands, and the
     * arm's own carriers reach further than that: a case may name a primitive, and a value written
     * as a number is not a construction. No model gets here that way — a declared sum's cases are
     * declared data, and the union that can name a primitive is anonymous and may not be written in
     * a narrow type position, so no container's element type has one. A language that let one be
     * written would arrive at the guard above rather than at a set with a member misfiled.
     *
     * <p>And nothing is narrowed to no members. An arm admitting none of what the container holds is
     * an arm no value reaches, so the name inside it stands for nothing — which is what a name with
     * no meaning here already says, and is not a set of no members.
     */
    private InputReads admitting(Core.Match match, Core.Case arm, Symbols symbols) {
        ReadMeaning.OneOf one = pluralityOf(match.scrutinee(), symbols);
        if (one == null) {
            return this;
        }
        for (souther.compiler.types.CaseSelector selector : arm.pattern().selectors()) {
            if (!(selector.refinement() instanceof souther.compiler.types.Refinement.Direct)) {
                return this;
            }
        }
        java.util.List<Denotation> left = new java.util.ArrayList<>();
        for (Denotation each : one.alternatives()) {
            souther.compiler.types.TypeSymbol written = caseWritten(each.value());
            if (written == null) {
                return this;
            }
            if (arm.caseTypes().contains(written)) {
                left.add(each);
            }
        }
        if (left.isEmpty()) {
            return this;
        }
        Map<BindingId, java.util.List<Denotation>> wider = new LinkedHashMap<>(alternatives);
        wider.put(arm.binder().binding(), left);
        return new InputReads(read, roots, bound, elements, wider, callsStand);
    }

    /**
     * The values {@code e} can stand for, or null where they are not written out.
     *
     * <p>Through the names that stand for one value, which is what a scrutinee usually is: a body
     * naming what it matches, and a helper expanded into one binding the call's argument to its own
     * parameter, leave a run of names between the {@code match} and the element. Read one step, an
     * arm inside such a helper would narrow nothing and the reading would stop at the first name.
     *
     * <p>Following is this reader's own and is not written into {@link #meaningOf}. That answers
     * what a name is, one step, for every reader; whether a reader may go on through a name that
     * stands for one value is what the answer licenses rather than something it does.
     *
     * <p>The same walk a container is found by ({@link #standing}), asked for what is standing at
     * the end of it rather than for a list written there. Two walks over the run of names between a
     * {@code match} and what it matches would be two answers about which names may be gone through,
     * and the day they differed the arm would narrow a set the arithmetic never met.
     */
    private ReadMeaning.OneOf pluralityOf(Core e, Symbols symbols) {
        Denotation standing = standing(new Denotation(e, this), symbols,
                new java.util.HashSet<>());
        return standing.value() instanceof Core.Read name
                && standing.at().meaningOf(name, symbols) instanceof ReadMeaning.OneOf one
                ? one : null;
    }

    /** Which case {@code e} is written as, or null where it is not written as one. */
    private static souther.compiler.types.TypeSymbol caseWritten(Core e) {
        return switch (e) {
            case Core.Construct nd -> nd.typeName();
            case Core.UnitValue unit -> unit.data();
            default -> null;
        };
    }

    /** The same, inside what {@code binder} binds. */
    @Override
    public InputReads and(Core.Binder binder, Core value) {
        if (binder == null || binder.binding() == null || value == null) {
            return this;
        }
        Map<BindingId, Core> wider = new LinkedHashMap<>(bound);
        // The nearest binding wins, which is what being inside it means.
        wider.put(binder.binding(), value);
        return new InputReads(read, roots, wider, elements, alternatives, callsStand);
    }

    /** The position {@code e} names here, or null where it names none. */
    @Override
    public TermPath pathOf(Core e, Symbols symbols) {
        return InputPath.of(e, roots, bound, elements, symbols, callsStand);
    }

    /**
     * What {@code read}'s name stands for here ({@link ReadMeaning}).
     *
     * <p>The one place a name is given a meaning for this side, and the whole of what this reading
     * knows about one. Every reader that meets a name asks here — the arithmetic that finds the line
     * a rule draws, and the walk that says which positions a rule mentions — so the two agree about
     * what a name is rather than each working out what a missing position meant.
     *
     * <p>A position first, wherever there is one. A name an operation handed an element on is a
     * position where the container is at one, and only where it is not does what the binding holds
     * matter — which is the order the position walk already reads them in, said here so a caller
     * does not have to know it.
     *
     * <p>What it holds is answered last and only as the expression. Whether that expression may
     * stand where the name does is the caller's question, asked of the fact rather than of a
     * permission recorded here: an arithmetic reader substitutes it, and a reader collecting
     * positions walks into it, and neither is the other's rule.
     *
     * <p>A set the arms already narrowed stands before an element's own, which is the same order as
     * everywhere else: what is in force where the name is read wins over what was true of it
     * further out.
     */
    public ReadMeaning meaningOf(Core.Read read, Symbols symbols) {
        return meaningOf(read, symbols, new java.util.HashSet<>());
    }

    /**
     * The same, through the bindings a walk into a container has already met.
     *
     * <p>One set for the whole answer, because the answer reaches back into this: a name an
     * operation handed an element on is answered by walking to the container it came from, and that
     * walk meets names this has to answer about. Threaded rather than started afresh at each step,
     * so what stops the walk is the bindings met and not a depth anybody chose.
     */
    private ReadMeaning meaningOf(Core.Read read, Symbols symbols,
                                  java.util.Set<BindingId> met) {
        TermPath path = pathOf(read, symbols);
        if (path != null) {
            return new ReadMeaning.Position(path);
        }
        java.util.List<Denotation> narrowed = alternatives.get(read.binding());
        if (narrowed != null) {
            return new ReadMeaning.OneOf(narrowed);
        }
        Core container = elements.containerOf(read.binding());
        if (container != null) {
            java.util.List<Denotation> written =
                    writtenElementsOf(new Denotation(container, this), symbols, met);
            return written == null ? new ReadMeaning.Element() : new ReadMeaning.OneOf(written);
        }
        Core held = bound.get(read.binding());
        // Read in this environment. Bindings are added on the way down and each tells itself from
        // every other, so what was bound after this name does not answer for what it holds — which
        // is why the environment at the binder and the one at the read cannot be told apart yet.
        // Said once here rather than by each reader, so the day they can be, one place changes.
        return held == null || held == read ? new ReadMeaning.Unknown()
                : new ReadMeaning.Through(new Denotation(held, this));
    }

    /**
     * The elements {@code container} was written with, or null where it was not written out.
     *
     * <p>What makes this an answer about every element and not about some of them is that the
     * container is followed only through steps with one successor — a name this environment bound,
     * and the body of a binding — until a list written in the source is standing there. An operation
     * that builds a container answers elements this walk cannot enumerate, and the walk stops rather
     * than reading what went in: {@code List.append(xs, ys)} holds the elements of both, and a
     * reading that took either would have written out a set missing the other half.
     *
     * <p><b>Followed with this environment and never with the body's.</b> What a binding holds is
     * also recorded over the whole body ({@link souther.compiler.check.ElementBindings#boundTo}), and
     * reading a container out of that would give a value with no environment to read it in — after
     * which the environment each element is read in would be whichever one the caller had in hand.
     * Where the way to the list runs through a binding this walk has not passed, the elements are
     * not written out, and that is a capability short of what a reader could have rather than a set
     * put together out of two readings.
     *
     * <p>Null for a list written empty. No value stands at an element of it, so there is nothing for
     * a statement about every member to be about, and a statement quantified over no members holds
     * whatever it says.
     */
    private static java.util.List<Denotation> writtenElementsOf(Denotation container,
                                                                Symbols symbols,
                                                                java.util.Set<BindingId> met) {
        Denotation standing = standing(container, symbols, met);
        if (!(standing.value() instanceof Core.ListLit written) || written.elements().isEmpty()) {
            return null;
        }
        java.util.List<Denotation> out = new java.util.ArrayList<>();
        written.elements().forEach(each -> out.add(new Denotation(each, standing.at())));
        return out;
    }

    /**
     * {@code from} followed through the steps that have one successor, as far as they go.
     *
     * <p>A name standing for one value and the body of a binding, and nothing else. A normal form
     * and never a failure: what comes back where nothing applies is what went in, which a caller
     * reads rather than treating as an absence.
     *
     * <p><b>Which names those are is {@link #meaningOf}'s answer and is not read off the bindings
     * here.</b> A name is a position, or one of several values, or an element, before it is what it
     * was bound to, and reading {@code bound} would be this walk deciding that order for itself —
     * beside the one place that decides it, and free to differ. No model here comes out differently
     * for it: what would tell them apart is a binding that both holds a value and is what an
     * operation handed an element on, which is a shape a fused pair of walks can leave
     * ({@link InputPath}) and which none of these tests writes.
     *
     * <p>By the bindings met, which is what makes it stop. Each tells itself from every other, so a
     * name that came round to itself is one already answered for.
     */
    private static Denotation standing(Denotation from, Symbols symbols,
                                       java.util.Set<BindingId> met) {
        Denotation at = from;
        while (true) {
            switch (at.value()) {
                case Core.Read name -> {
                    if (!met.add(name.binding())
                            || !(at.at().meaningOf(name, symbols, met)
                                    instanceof ReadMeaning.Through through)) {
                        return at;
                    }
                    at = through.denotes();
                }
                case Core.LetIn let ->
                        at = new Denotation(let.body(), at.at().and(let.binder(), let.value()));
                default -> {
                    return at;
                }
            }
        }
    }

    /** The position an element handed to {@code binding} stands at, or null where it stands at
     *  none ({@link InputPath#elementAt}). */
    public TermPath elementAt(BindingId binding, Symbols symbols) {
        return InputPath.elementAt(binding, roots, bound, elements, symbols, callsStand);
    }

    /** The position {@code e}'s value came from, or null where it came from none. Not where it is:
     *  a value made from a position is not that position ({@link InputPath#cameFrom}). */
    public TermPath cameFrom(Core e, Symbols symbols) {
        return InputPath.cameFrom(e, roots, bound, elements, symbols, callsStand);
    }
}
