package souther.compiler.inputs;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.Shape;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeView;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.compiler.values.AdmissibleSet;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What can arrive at each position of one behavior's input, read once.
 *
 * <p>The single answer four measures are projections of. What cases a signature is owed, what
 * classes a position divides into, what arms a row is owed and what a body's {@code unreachable}
 * claims are held against all come from here — derived separately they disagreed, and the disagreement
 * had a direction: the reading that knew about the rules refused a case, and the reading that knew
 * only the type asked for a row at it.
 *
 * <p><b>The walk is here and not in a reader.</b> A reader with its own walk has its own set of
 * positions, and a position one of them never visited is one it can say nothing about while another
 * answers for it. So every position a behavior's input has is read, whatever any reader goes on to
 * do with it — including the ones a reader gives up in favour of what is under them, and the ones
 * dropped past a budget.
 *
 * <p>Which is a claim about the reading and not about the step it is made of. What stands directly
 * under a type is one fact and is {@link StructuralDescent}'s; how far to follow it, and what is
 * read where it lands, are this reading's. A reader wanting the step alone
 * takes it from there, and takes none of the meaning here with it.
 *
 * <p><b>A position may exist only under a narrowing of another.</b> What a case of a sum declares is
 * declared whether or not anything constructs one, so those fields are positions of the input and are
 * read here — at a path carrying the narrowing they stand under ({@link Refinement}), which is what
 * says a row has to be that case for them to be reached at all. Which branches are walked is settled
 * by what the position came back owing rather than by what its type has: a case the rules refuse has
 * no positions to cover, exactly as a value whose rules contradict has none.
 *
 * <p><b>Where a value is built is still not one of these positions.</b> The generator goes on until
 * there is a value to build, which is further down than a report is about. Those paths are written the
 * same way and are about something else, so they are never looked up here.
 *
 * <p>Nothing a body writes reaches this. A {@code guard}'s line, a {@code match} arm and an
 * {@code unreachable} are statements about the same positions and are read against this rather than
 * into it — which is what keeps a body from moving the denominator it is measured by.
 */
public final class InputDomain {

    /** How deep <em>this reading</em> takes a product apart. Two levels reach a field of a record a
     * parameter holds, which is where domain rules are written; below that a report stops being
     * about anything the author would recognise as one input.
     *
     * <p>An answer about reports and not about types. What is under a position this stops at is
     * still there and is still {@link StructuralDescent}'s to say — a value has to be built at
     * positions four levels down, and that reader asks for what it needs rather than being told the
     * model puts nothing there. Written as a property of the walk, it was the second thing every
     * such reader had to work around. */
    public static final int MAX_DEPTH = 2;

    /**
     * The declaration a position's rules are read of, and where that value stands.
     *
     * <p>One reading per rule-owning value and not one per record met on the way down: a clause on
     * the outer record relates positions at any depth it can name, and rebuilding the reading at
     * each record is how a clause stopped reaching the field it was about.
     *
     * <p><b>What starts a new one is a descent crossing a boundary of rule ownership</b>, which is
     * wherever the value below is one a declaration writes its own clauses about. Narrowing into a
     * case is one — what a {@code GlobalQuery} says about its {@code tag} is written in
     * {@code GlobalQuery} and cannot be written in the sum — and so is entering what a sequence
     * holds, since what {@code Tag} says about itself is written in {@code Tag} however the position
     * is reached. Both go through {@link #takeTheRulesOver} and nothing else does, which is what a
     * shape this compiler learns to walk later has to do to have its rules read at all (#1072).
     *
     * <p>Kept as the declarations rather than as a reading of them, for the reason the parameters
     * are: what is answered with is compared as a value by whatever decides that a compile changed
     * nothing.
     */
    public record RuleRoot(TermPath at, Type type) {}

    /** Nothing to read: a behavior whose signature is not in hand. */
    public static final InputDomain NONE =
            new InputDomain(List.of(), Map.of(), List.of(), List.of(), null, NameReach.NONE,
                    List.of());

    private final List<Position> positions;
    private final Map<TermPath, Position> byPath;
    private final Map<BindingId, String> read;
    /** What the behavior takes, kept as it was written. Values and nothing else: what is answered
     * with is compared as a value by whatever decides an edit changed nothing, and a reading holds a
     * way of reading the declarations rather than a statement about them. */
    private final List<Parameter> parameters;
    /** Every declaration whose rules reach a position of this input, and where it stands. One per
     * parameter, and one more wherever a descent crossed a boundary of rule ownership — see
     * {@link RuleRoot}. */
    private final List<RuleRoot> roots;
    private final ReadingPolicy policy;
    /** Where a name written at one position stands, wherever that is not the position of the same
     * name one step down. Made by the walk that made the positions, so that what a name reaches and
     * what the reading produced are one answer. */
    private final NameReach reach;
    /** Everything the rules of the values this reading opened placed, in the words each of them was
     * written in. What became of each is {@link #placements()}. */
    private final List<PlacementSeed> placed;

    private InputDomain(List<Position> positions, Map<BindingId, String> read,
                        List<Parameter> parameters, List<RuleRoot> roots, ReadingPolicy policy,
                        NameReach reach, List<PlacementSeed> placed) {
        this.placed = List.copyOf(placed);
        this.positions = List.copyOf(positions);
        this.read = Map.copyOf(read);
        this.parameters = List.copyOf(parameters);
        this.roots = List.copyOf(roots);
        this.policy = policy;
        this.reach = reach;
        Map<TermPath, Position> at = new LinkedHashMap<>();
        // The first reading of a path stands. A path is where a rule and a row meet, so two
        // readings under one path would be the position answering differently depending on which
        // reader looked it up.
        positions.forEach(each -> at.putIfAbsent(each.path(), each));
        this.byPath = Map.copyOf(at);
    }

    /**
     * One thing a behavior is applied to: what it is called, what it holds, and which binding a body
     * reads it as.
     *
     * <p>Taken together because they are one fact — three lists a caller can get out of step is how
     * a position comes to be named after one parameter and read off another.
     *
     * @param name    what a report calls the position, which is the name the <em>declaration</em>
     *                wrote: a behavior states what it takes, and an implementation may bind the same
     *                thing under another spelling
     * @param binding what a body's reads of it carry, or null where no implementation binds it. What
     *                a binding is cannot be worked out from how it was spelled ({@link BindingId}),
     *                which is why the two are both here and neither stands in for the other
     */
    public record Parameter(String name, BindingId binding, Type type) {}

    /** Every position of an input, in the order the parameters are declared and descended into. */
    public static InputDomain of(List<Parameter> parameters, Symbols symbols,
                                 ReadingPolicy policy) {
        List<Position> found = new ArrayList<>();
        List<RuleRoot> roots = new ArrayList<>();
        Map<BindingId, String> read = new LinkedHashMap<>();
        // Where a reading ended with the rules under a position still to be read, and what took
        // them over. Kept across the whole walk because the two halves happen at different steps of
        // it: the reading says it stopped as the position is read, and the descent says who took
        // the rules as it opens the reading that did.
        RuleHandoffs handoffs = new RuleHandoffs();
        // Written as the positions are made, so that a name reaches a position exactly where this
        // walk produced one.
        NameReach.Observed observed = new NameReach.Observed();
        // Everything the rules of every value this reading opened placed, gathered as each reading
        // is opened. What became of each of them is asked once the positions are all in hand.
        List<PlacementSeed> account = new ArrayList<>();
        for (Parameter parameter : parameters) {
            if (parameter.binding() != null) {
                read.putIfAbsent(parameter.binding(), parameter.name());
            }
            TermPath at = TermPath.of(parameter.name());
            roots.add(new RuleRoot(at, parameter.type()));
            PlacedRules rules = PlacedRules.of(at, parameter.type(), symbols, policy);
            account.addAll(rules.placed());
            walk(at, parameter.type(), 0, symbols, policy, rules, found, roots,
                    java.util.Set.of(), handoffs, observed, account);
        }
        // And only now, because a handoff is discharged by a descent that happens after the
        // position above it has been read. Held the other way round, every position that hands its
        // rules on would have to be read after everything under it, and the order positions are
        // reported in is the order they are declared and descended into.
        List<Position> settled = found.stream()
                .map(each -> shortOfHandedOnRules(each, handoffs.unresolvedAt(each.path())))
                .toList();
        return settled.isEmpty() ? NONE
                : new InputDomain(settled, read, parameters, roots, policy, observed.reach(),
                        List.copyOf(account));
    }

    /**
     * The same, of a behavior and the implementation that binds its parameters.
     *
     * <p>The one place the three are put side by side: the declaration says what the parameters are
     * called, the signature says what they hold, and the implementation says which binding a body's
     * reads of one carry. Paired here rather than by every caller that has some of them.
     *
     * @param fn the implementation, or null where nothing implements this behavior — an injected
     *           behavior has positions and no body to read them in
     */
    public static InputDomain of(Hir.SpecBehavior behavior, Hir.FnDef fn, Sig sig,
                                 Symbols symbols, ReadingPolicy policy) {
        List<Parameter> parameters = new ArrayList<>();
        for (int i = 0; i < sig.inputTypes().size() && i < behavior.params().size(); i++) {
            BindingId binding = fn != null && i < fn.params().size()
                    ? fn.params().get(i).binder().binding() : null;
            parameters.add(new Parameter(behavior.params().get(i).name(), binding,
                    sig.inputTypes().get(i)));
        }
        return of(parameters, symbols, policy);
    }

    /**
     * The same, of an input nothing reads a body against.
     *
     * <p>The positions are the same either way — what a behavior takes is what it declares — and
     * what is absent is the means to tell one of its parameters from a name a body binds under the
     * same spelling. So this is the reading for a caller with no body in hand, and a caller with one
     * that used it would find every claim and every comparison naming nothing.
     */
    public static InputDomain of(Hir.SpecBehavior behavior, Sig sig, Symbols symbols,
                                 ReadingPolicy policy) {
        return of(behavior, null, sig, symbols, policy);
    }

    /** The positions, in the order they were read. */
    public List<Position> positions() {
        return positions;
    }

    /**
     * The position at {@code path}, or null where this reading has none there.
     *
     * <p>Null for two unlike paths: one below where this reading stops, and one that is not a
     * position of this behavior at all. Neither is a path a value is built at — those are the
     * generator's and are not looked up here, because a construction recipe puts positions under a
     * sum where the declaration has none and no reading of the declaration would ever hold them.
     */
    public Position at(TermPath path) {
        return byPath.get(path);
    }

    /** Where a name written at one position stands, as this walk observed it. */
    public NameReach reach() {
        return reach;
    }

    /**
     * Everything the rules of this input's values placed, and what became of each of them.
     *
     * <p>The whole of what a build has to account for on this side. Every rule that placed anything
     * is here, and every one of them ends somewhere said out loud — filed at a position, refused by
     * the reading, or left with nowhere to go and a reason for it. Counted from the filings alone, a
     * rule this compiler had nowhere to put would be a rule nobody wrote.
     */
    public List<PlacementFiling> placements() {
        List<PlacementFiling> out = new ArrayList<>();
        for (PlacementSeed each : placed) {
            out.add(file(each));
        }
        return List.copyOf(out);
    }

    /**
     * Every position the dotted name {@code named}, written in the rules of the value at
     * {@code root}, stands at.
     *
     * <p>One name and any number of positions. A name is written once and a value is of one case, so
     * a name naming a field the cases of a sum share stands under each of them — and where two such
     * sums are on the way, at each pairing of their cases. Which is why this is taken a step at a
     * time against what the walk observed rather than by rewriting the name and reading the types
     * again: crossing at the first sum settles which positions the second step is asked of.
     *
     * <p>Empty where nothing this walk produced answers to the name. That is the whole of what is
     * said: a case the reading left, a field below where it stops and a name of nothing at all are
     * not told apart here, and a caller that has to tell them apart asks {@link #reach} what became
     * of each case.
     */
    public List<TermPath> positionsNamed(TermPath root, String named) {
        return follow(root, named).reached();
    }

    /**
     * What becomes of {@code seed} at every place the name it was written at reaches.
     *
     * <p>The one crossing from what a rule wrote to where a row goes. Everything a rule places comes
     * through here — an end a clause put on a number, the values a clause admits, a line a body drew
     * — because what differs between them is what is said and never where, and a second reading of
     * where would be a second answer to which rules reach which positions.
     *
     * <p>Never nothing. A name that reaches no position comes back saying so, with what the reading
     * was left with at the position it stopped at, so that a reader further on never has an absence
     * to make a cause out of.
     */
    public PlacementFiling file(PlacementSeed seed) {
        Followed followed = follow(seed.address().root(), seed.address().key());
        List<PlacementOutcome> outcomes = new ArrayList<>();
        followed.reached().forEach(each -> outcomes.add(
                new PlacementOutcome.Filed(new PositionId(each))));
        outcomes.addAll(followed.otherwise());
        return new PlacementFiling(seed, outcomes);
    }

    /** Where following a name got to, and what became of it everywhere it did not get to. */
    private record Followed(List<TermPath> reached, List<PlacementOutcome> otherwise) {}

    /**
     * Follow a name from the value it was written in, a step at a time.
     *
     * <p>A step at a time and not by rewriting the name: crossing at the first sum settles which
     * positions the next step is asked of, so a name naming a field two shared sums down stands at
     * every pairing of their cases. Composed from the whole name at once, the pairing would be
     * something this had to work out rather than something it walks into.
     */
    private Followed follow(TermPath root, String named) {
        List<PlacementOutcome> otherwise = new ArrayList<>();
        List<TermPath> frontier = List.of(root);
        // The value's own name is at no step of its own, and a name of no steps is not a step
        // called nothing.
        for (String step : named.isEmpty() ? new String[0] : named.split("\\.")) {
            List<TermPath> next = new ArrayList<>();
            for (TermPath at : frontier) {
                List<TermPath> across = reach.across(at, step);
                List<NameReach.NotStanding> stopped = reach.notStanding(at, step);
                if (!across.isEmpty() || !stopped.isEmpty()) {
                    next.addAll(across);
                    // Under this case the name stands nowhere, and the reading of the case said
                    // where it stopped. One per case, since the readings need not have stopped
                    // alike.
                    stopped.forEach(each -> otherwise.add(new PlacementOutcome.Unresolved(
                            new PlacementOutcome.Reason.TheReadingStoppedThere(
                                    new PositionId(at.refine(each.branch())), each.why()))));
                    // A name crossing into the cases reaches every case, so a case the reading left
                    // is a place this name got to and stops at. Read from what the walk wrote down
                    // about that case, never from the name having one place fewer to stand.
                    reach.branchesNotEntered().stream()
                            .filter(each -> each.at().equals(at))
                            .forEach(each -> otherwise.add(new PlacementOutcome.Refused(each)));
                    continue;
                }
                // An ordinary name, which is at the position of that name one step down — and only
                // where the walk made one.
                TermPath under = at.then(step);
                if (byPath.containsKey(under)) {
                    next.add(under);
                } else {
                    otherwise.add(new PlacementOutcome.Unresolved(whyNothingAt(at, step)));
                }
            }
            frontier = next;
        }
        return new Followed(List.copyOf(frontier), List.copyOf(otherwise));
    }

    /**
     * What the reading was left with where a name stopped.
     *
     * <p>The position's own answer and not a second opinion about it. A reading that stopped says so
     * where it stopped ({@link StructuralInspection.Continuation.Blocked}), and that is what an
     * author is owed; where it did not stop, what is left is that nothing of the name is there, which
     * says that and nothing more.
     */
    private PlacementOutcome.Reason whyNothingAt(TermPath at, String step) {
        Position position = byPath.get(at);
        if (position != null
                && position.structure() instanceof StructuralInspection.Retained retained
                && retained.continuation()
                        instanceof StructuralInspection.Continuation.Blocked blocked) {
            return new PlacementOutcome.Reason.TheReadingStoppedThere(
                    new PositionId(at), blocked.why());
        }
        return new PlacementOutcome.Reason.NothingOfThatNameThere(new PositionId(at), step);
    }

    /**
     * The order one term is read off a row and written back on, or null where it has none.
     *
     * <p><b>The one answer, so that nothing derives it from an expression.</b> A rule is written
     * beside operands, and the type of an operand is not the type of the position the rule is about:
     * an operation the arithmetic rewrote into a form of two positions is compared as what it
     * answers with, so {@code Date.daysBetween(a, b) > 10} has {@code Int} on both sides and dates
     * at both positions. Read off the comparison, every position of that rule was written back as a
     * whole number and read off a row as one, and both directions agreed with each other and with
     * nothing else (#1018).
     *
     * <p>Two questions, answered where each is known. What a term measures is the term's — a size is
     * a whole number whatever it is taken of — and what the location holds is this reading's, which
     * is why the two meet here rather than at whichever caller had both to hand.
     *
     * <p><b>A term under no position of this reading still has an order.</b> This reading stops at
     * {@link #MAX_DEPTH}, where a report stops being about anything an author would call one input,
     * and nothing stops a rule from naming what is under that. What a report is about and what a
     * declaration says are two questions, and only the first of them stops there — so the type is
     * followed down to wherever the rule named ({@link #declaredAt}) and the line is drawn.
     *
     * <p>The position first and the descent only where there is none. A position may stand under a
     * narrowing, and what it holds there is what a row writes; walking the declaration again would
     * answer with what the field was declared as before anything narrowed it.
     */
    public Carrier answeredOn(NumericTerm term, Symbols symbols) {
        return ordersOf(term, symbols).answered();
    }

    /**
     * The order a value at {@code term}'s path is read off a row on, or null where nothing orders
     * it.
     *
     * <p>The other end of the same term, and never the one above. What a term answers and what it is
     * read off are two orders for every term that is what an operation answered and one order for
     * every term that is not — so a caller handed a single carrier had whichever of the two the
     * caller before it meant, and the day the two part is the day a row is decoded on a count the
     * value is not written in (#1027).
     */
    public Carrier observedOn(NumericTerm term, Symbols symbols) {
        return ordersOf(term, symbols).observed();
    }

    /** Both ends of one term, taken together from the one reading of where it sits. */
    public TermOrders ordersOf(NumericTerm term, Symbols symbols) {
        return term.ordersAt(typeAt(term.path(), symbols), symbols);
    }

    /**
     * What stands at {@code path} as this reading has it, or null where it reaches nothing there.
     *
     * <p>The position first and the declarations only where there is none, which is the one
     * resolution of where a term sits. A caller that walked the declarations itself would answer
     * with what a field was declared as before anything narrowed it, and a caller that took the
     * position alone would have nothing under {@link #MAX_DEPTH}. Both readers of this — what a term
     * is measured on, and whether an operation may be taken of it — get the same answer because
     * there is one.
     */
    public Type typeAt(TermPath path, Symbols symbols) {
        Position position = at(path);
        return position != null ? position.type() : declaredAt(path, symbols);
    }

    /**
     * What the declarations put at {@code path}, however far down it goes, or null where they put
     * nothing this can follow.
     *
     * <p>Below {@link #MAX_DEPTH} this is the only answer there is: the walk above stopped, so there
     * is no position to ask and the type is what the declaration says at each step.
     *
     * <p>Step by step through {@link StructuralInspection}, which is what the walk above takes its
     * own steps from. What is under a type is one fact, and a second reading of it here would be
     * this and that walk disagreeing about what a path reaches — which is the shape of defect this
     * whole change is about, one level down.
     */
    private Type declaredAt(TermPath path, Symbols symbols) {
        Type here = null;
        for (Parameter parameter : parameters) {
            if (parameter.name().equals(path.head())) {
                here = parameter.type();
                break;
            }
        }
        for (TermPath.Step step : path.steps()) {
            here = here == null ? null : under(here, step, symbols);
        }
        return here;
    }

    /**
     * What one step of a path stands at, or null where the declarations put nothing there.
     *
     * <p><b>Exhaustive over the kinds of step, with no {@code default}.</b> A path goes into a
     * field, into what a sequence holds, or nowhere at all while narrowing which values may stand
     * where it already is ({@link Refinement}) — three, and a reading that answered one of them and
     * let the rest fall to null would lose a line the model draws for every path carrying one. It
     * did: written for fields alone, a rule comparing two fields of a list's elements was read as
     * naming nothing, and the border it draws went away. A fourth kind is a compile error here
     * rather than a fourth quiet absence.
     */
    private static Type under(Type type, TermPath.Step step, Symbols symbols) {
        TypeView view = TypeView.of(type, symbols);
        // Asked of the shape rather than through the proof a position is made with. What is under a
        // type is a question about the type, and a type nothing can be read at answers nothing here
        // rather than being refused as a position this compiler disagrees with itself about.
        if (!(view.shape() instanceof Shape.ReadablePositionShape shape)) {
            return null;
        }
        StructuralInspection under =
                StructuralInspection.of(shape, true, Distinctions.ofType(view, symbols));
        return switch (step) {
            // A field of a record, or a name a sum's cases all spread. The second is readable on a
            // value of the sum without opening a case, so the model does put something at it, and a
            // reading that answered for the first alone would say the model puts nothing where the
            // language reads a value.
            case TermPath.Step.Field field -> under instanceof StructuralInspection.Decomposed made
                    ? made.under().get(field.name())
                    : sharedFieldsOf(shape).get(field.name());
            case TermPath.Step.Element _ -> under instanceof StructuralInspection.Retained on
                    && on.continuation() instanceof StructuralInspection.Continuation.Elements held
                    ? held.element() : null;
            // The same position, read as the case it turned out to be. Null where the case puts
            // nothing there, which is a case that is the whole of a value.
            case TermPath.Step.Refine refine -> under instanceof StructuralInspection.Retained on
                    && on.continuation() instanceof StructuralInspection.Continuation.Branches ways
                    ? narrowed(ways, refine.refinement()) : null;
        };
    }

    /** The type the branch for this narrowing stands at, or null where the sum has no such branch. */
    private static Type narrowed(StructuralInspection.Continuation.Branches ways,
                                 Refinement refinement) {
        for (StructuralInspection.Branch branch : ways.branches()) {
            if (refinement.equals(branch.refinement())) {
                return branch.under();
            }
        }
        return null;
    }

    /**
     * The same input, asked about a quantity over several of its positions.
     *
     * <p>The relational half of what a reading of an input can say. A {@link Position} answers about
     * itself, and a rule relating two of them divides neither — so a caller holding a form asks here
     * rather than composing the positions' answers, which cannot carry a relation whatever each of
     * them says.
     *
     * <p><b>A capability, and not part of what this answers with.</b> Asking the declarations a
     * further question takes a way of reading them, and what is answered with is compared as a value
     * by whatever decides that a compile changed nothing — so this is built where it is used and
     * never kept here. Which is also why it takes the symbols rather than holding them: the reading
     * of an input says what it says, and this is how something else goes on asking.
     *
     * <p><b>Once per reader.</b> What comes back reads each parameter's declarations, so a caller
     * that built one per comparison would read every parameter of every behavior once per
     * comparison written about it. Built at the top of whatever is walking, and handed down.
     */
    public Quantities quantities(Symbols symbols) {
        Map<TermPath, PlacedRules> byRoot = new LinkedHashMap<>();
        for (RuleRoot root : roots) {
            // The first reading under a path stands, for the same reason the first reading of a
            // position does: two roots at one path would be one place answering differently
            // depending on which reader looked it up.
            byRoot.computeIfAbsent(root.at(),
                    at -> PlacedRules.of(at, root.type(), symbols, policy));
        }
        return ReadQuantities.of(byRoot, byRoot.keySet(), byPath, symbols);
    }

    /**
     * What a body's read of {@code binding} names, or null where it is not one of these parameters.
     *
     * <p>Asked of the binding and never of the spelling. A body may bind a name its own behavior
     * already binds — {@code let f = defaulted(f)} — and the two are different values under one
     * word, so a reader matching the word reads the inner one as the outer.
     */
    public String parameterRead(BindingId binding) {
        return binding == null ? null : read.get(binding);
    }

    /**
     * The same, as the whole map, for a reader that walks a tree rather than asking about one
     * binding.
     *
     * <p>A behavior's parameters are bound more than once. The implementation binds them where the
     * body reads them, and the declaration binds them where its own {@code ensures} clauses do; a
     * reading is handed the bindings of the tree it is walking, and one given the others finds every
     * comparison about nothing. What is here is the implementation's, which is what this reading was
     * made from.
     */
    public Map<BindingId, String> parameterReads() {
        return read;
    }

    /**
     * {@code position} with the rules it handed on counted as unread, because nothing took them.
     *
     * <p>Made here and not asked of the position, which does not know it. A reading of a value ends
     * where no declaration stands to be read and the rules under the position become another
     * reading's; whether one was opened is settled by the descent past this position, and that
     * happens after the position has been read and reported. Answering it would be a way to write a
     * {@link Position} down, and there being no such way is what keeps one position to one answer.
     *
     * <p>Read off the ledger and not off whether a reading exists somewhere under the path: an
     * obligation discharged by whatever happens to be below it is one no descent ever had to meet
     * ({@link RuleHandoffs}).
     *
     * <p><b>This is where the two readings are joined, and the only place that may be.</b> The
     * ledger knows that no recipient was named; the structural reading knows whether the walk could
     * go into the position at all. Neither is the provenance on its own, and whoever asked later
     * would be joining whatever state each phase still happened to be holding — which for the
     * structural side is nothing, since a position a body's rule measures keeps no continuation
     * (issue #1084). So the answer is settled here and carried from here.
     *
     * <p>Added to whatever the position already found. A reading that lost a clause of its own and
     * handed rules on that nobody took is short of both, and answering with the first was how the
     * second went missing.
     */
    private static Position shortOfHandedOnRules(Position position,
                                                 RuleHandoffs.Shortfall shortfall) {
        if (shortfall == null) {
            return position;
        }
        ReadPosition read = (ReadPosition) position;
        BlockedDescent blocked = BlockedDescent.of(read.structure());
        RulesLeftUnread.HandoffUnread why = switch (shortfall) {
            case RuleHandoffs.Shortfall.NothingExpected _ ->
                    new RulesLeftUnread.HandoffUnread.FromBlockedDescent();
            case RuleHandoffs.Shortfall.NotFullyAccepted _ ->
                    new RulesLeftUnread.HandoffUnread.NotFullyAccepted();
        };
        // The whole agreement and not the half this arm happens to need. Over an owed handing over,
        // nobody was named as a recipient exactly where the walk could not go in — so a ledger that
        // named nobody at a position this entered and a ledger that named somebody at a position it
        // could not enter are both two walks over one model disagreeing about one path, joined by
        // the spelling of it. Held one way, the second would arrive as an arm nothing folds beside a
        // descent that is reported, which is #1084's own two entries, reached by a different road.
        if (why.namesABlockedDescent() != (blocked != null)) {
            throw new IllegalStateException(
                    "the ledger and the walk disagree at " + read.path() + ": " + shortfall
                            + " beside " + read.structure());
        }
        java.util.Set<RulesLeftUnread> left =
                new java.util.LinkedHashSet<>(read.rulesLeftUnread());
        left.add(new RulesLeftUnread.Handoff(why));
        return new ReadPosition(read.path(), read.view(), read.term(), read.numericDomain(),
                read.ownEnds(), read.narrowedEnds(), read.rangeLeft(), read.narrowedLower(),
                read.narrowedUpper(), read.nothingExists(), read.projection(),
                read.declared(), read.reading(), read.obligations(), read.completeness(),
                read.valuesUnread(), read.rulesWithoutALine(), read.unansweredQuestions(),
                left, read.structure());
    }

    /**
     * One position, read, and then what is under it.
     *
     * <p>What is under a position is walked whether or not the position itself came to anything.
     * Only a product has children, and a product states no distinction of its own and carries no
     * end, so nothing is read here that a reader would have to weigh against the position above
     * it — and a reader that gives a position up in favour of its fields finds them read either
     * way.
     */
    private static void walk(TermPath path, Type type, int depth, Symbols symbols,
                             ReadingPolicy policy, PlacedRules placed, List<Position> found,
                             List<RuleRoot> roots, java.util.Set<Type> visited,
                             RuleHandoffs handoffs, NameReach.Observed observed,
                             List<PlacementSeed> account) {
        // The proof first, and before anything is read off the position. A shape a reading is not
        // made of is this compiler disagreeing with itself about what may stand at a position, and
        // it is refused here rather than arriving further down as a position nothing divides.
        ReadablePosition input = ReadablePosition.of(TypeView.of(type, symbols));
        // What the position's type states, read once and handed to both readings of it. What a sum's
        // cases are decides which classes the position has and which branches stand under it, and a
        // second reading of that here would be the two disagreeing about which cases there are.
        List<Case> declared = Distinctions.ofType(input.view(), symbols);
        StructuralInspection structure =
                StructuralInspection.of(input.shape(), depth < MAX_DEPTH, declared);
        Position here = read(input, path, symbols, placed, structure, declared);
        found.add(here);
        // Said as the position is read and before anything under it is walked, so that a descent
        // that never happens leaves the obligation standing rather than never making one.
        if (placed.handsTheRulesOnAt(path)) {
            handoffs.owes(placed.root(), path);
        }
        switch (structure) {
            case StructuralInspection.Decomposed decomposed -> {
                for (Map.Entry<String, Type> field : decomposed.under().entrySet()) {
                    walk(path.then(field.getKey()), field.getValue(), depth + 1, symbols, policy,
                            // A field is a value of its own, so a sum met under it is one this walk
                            // has not taken apart however many were taken apart above.
                            placed, found, roots, java.util.Set.of(), handoffs, observed, account);
                }
            }
            case StructuralInspection.Retained retained ->
                    under(retained.continuation(), here, path, sharedAt(input), depth, symbols,
                            policy, placed, found, roots, visited, handoffs, observed, account);
        }
    }

    /**
     * The names readable at this position that a value of one of its cases carries, which is empty
     * for every position but a sum whose cases all spread one declaration.
     *
     * <p>Read off {@link Shape.Sum#common}, which is the same answer that makes those names readable
     * on a value of the sum at all. Taken from what a case declares instead, a field one case has
     * and another has not would be a name this said could be written at the sum, and the reading
     * would reach positions the language refuses to name.
     */
    private static List<String> sharedAt(ReadablePosition input) {
        return List.copyOf(sharedFieldsOf(input.shape()).keySet());
    }

    /**
     * The names a value of this shape carries that are readable on it without opening a case, and
     * what stands at each.
     *
     * <p>The one reading of a sum's shared part in this walk. What makes a name readable on a value
     * of the sum is the declarations its cases all spread, and every question here that turns on
     * that name — which names cross a narrowing, and what the model puts at one — is asked of this.
     * Empty for every other shape, whose names are the positions under it.
     */
    private static Map<String, Type> sharedFieldsOf(Shape shape) {
        return shape instanceof Shape.Sum sum
                && sum.common() instanceof Shape.CommonProduct.Shared shared
                ? shared.fields() : Map.of();
    }

    /**
     * What follows a position that stands, walked.
     *
     * <p>Beside the position and never instead of it: what a list holds is read, and the list is
     * still a position with a length of its own that this reading has already answered for; a case
     * puts positions under the sum, and the sum still divides into its cases.
     *
     * <p><b>Owed and not merely declared.</b> A case the rules refuse has no positions to cover —
     * every field of it is a row nobody can write — and the branches walked are the ones the
     * position came back owing, so that what a report counts at the position and what it measures
     * under it come from one reading of it. Which is also why the widening the obligations may have
     * applied travels with them: where the rules were set aside, they are set aside for the
     * positions under the case as much as for the case.
     *
     * <p>And it is where the rules the position handed on are passed to somebody. Which positions
     * they are passed to is settled here, from the branches this position is owed at — never worked
     * out afterwards from the readings that exist, since a reading opened under the position for
     * some other reason is not one anybody handed anything to.
     */
    private static void under(StructuralInspection.Continuation continuation, Position here,
                              TermPath path, List<String> shared, int depth, Symbols symbols,
                              ReadingPolicy policy,
                              PlacedRules placed, List<Position> found, List<RuleRoot> roots,
                              java.util.Set<Type> visited, RuleHandoffs handoffs,
                              NameReach.Observed observed, List<PlacementSeed> account) {
        switch (continuation) {
            // Nothing is opened under the position, so a handoff made there stays standing. Which
            // is the answer whichever of the two this is: a shape this compiler does not enter and
            // a depth this walk stops at both leave the rules under it read by nobody.
            case StructuralInspection.Continuation.None _,
                 StructuralInspection.Continuation.Blocked _ -> { }
            case StructuralInspection.Continuation.Elements elements -> {
                TermPath at = path.element();
                handoffs.passesTo(placed.root(), path, List.of(at));
                // Nothing crosses into what a sequence holds: what a clause of the value out here
                // says is written about the sequence, and an element is a value with a declaration
                // of its own.
                takeTheRulesOver(placed.root(), path, at, elements.element(), depth + 1, symbols,
                        policy, found, roots, java.util.Set.of(), handoffs, observed, null,
                        account);
            }
            case StructuralInspection.Continuation.Branches branches -> {
                List<StructuralInspection.Branch> standing = new ArrayList<>();
                List<TermPath> passedTo = new ArrayList<>();
                for (StructuralInspection.Branch branch : branches.branches()) {
                    // A branch that is the whole of a value puts no position anywhere, and one the
                    // rules leave nothing at has no row to be written at it. Neither is a place the
                    // rules were passed to, so neither is owed a reading.
                    if (branch.under() == null) {
                        // A name has nowhere to stand under a case that holds nothing, which is not
                        // a shortfall and is not the answer below. Said apart from it so that a
                        // reader of what became of this case reads which it was.
                        observed.didNotEnter(path, branch.refinement(),
                                new NameReach.NotEntered.NothingStandsUnderIt());
                        continue;
                    }
                    if (!owed(here, branch.refinement())) {
                        observed.didNotEnter(path, branch.refinement(),
                                new NameReach.NotEntered.TheRulesLeaveNothingAtIt());
                        continue;
                    }
                    standing.add(branch);
                    passedTo.add(path.refine(branch.refinement()));
                }
                handoffs.passesTo(placed.root(), path, passedTo);
                for (StructuralInspection.Branch branch : standing) {
                    int before = found.size();
                    // What the value above calls the positions under this case, where it calls them
                    // anything: the names its cases share and nothing else. Handed down as the
                    // reading of the case is opened, so a clause written above is read at the
                    // position it is about by the one reading of that position.
                    PlacedRules.Reaching crossing = shared.isEmpty() ? null
                            : new PlacedRules.Reaching(placed, path, branch.refinement(),
                                    new java.util.LinkedHashSet<>(shared));
                    walkBranch(branch, placed.root(), path, depth, symbols, policy, found, roots,
                            visited, handoffs, observed, crossing, account);
                    crossed(observed, path, shared, branch.refinement(), found, before);
                }
            }
        }
    }

    /**
     * Say where the names the cases share stand, now that this case has been walked.
     *
     * <p>Asked of the positions this branch just produced, which is what keeps a crossing from
     * naming a position nobody made: a field deeper than this reading goes and a case it turned back
     * out of both leave the name with one place fewer to stand, and neither leaves a crossing to be
     * read as one.
     *
     * @param from  where the walk's positions began before this branch was walked, so that what is
     *              looked through is what this branch put there
     */
    private static void crossed(NameReach.Observed observed, TermPath at, List<String> shared,
                                Refinement branch, List<Position> found, int from) {
        if (shared.isEmpty()) {
            return;
        }
        TermPath narrowed = at.refine(branch);
        List<Position> made = found.subList(from, found.size());
        for (String field : shared) {
            TermPath stands = narrowed.then(field);
            if (made.stream().anyMatch(each -> each.path().equals(stands))) {
                observed.crosses(at, field, branch, stands);
                continue;
            }
            // Nowhere under this case, and the reading of the case is what says why. Asked of the
            // sum instead, there would be nothing to say: a sum is read whatever the depth, so its
            // silence would be read as the model putting no such field here.
            BlockReason.AboutThePosition why = whereItStopped(made, narrowed);
            if (why != null) {
                observed.doesNotStand(at, field, branch, why);
            }
        }
    }

    /** What the reading of the case standing at {@code narrowed} was left with, or null where it was
     *  not left with anything — which is a case that was read to the end. */
    private static BlockReason.AboutThePosition whereItStopped(List<Position> made,
                                                               TermPath narrowed) {
        for (Position each : made) {
            if (each.path().equals(narrowed)
                    && each.structure() instanceof StructuralInspection.Retained retained
                    && retained.continuation()
                            instanceof StructuralInspection.Continuation.Blocked blocked) {
                return blocked.why();
            }
        }
        return null;
    }

    /**
     * Open a reading at a position the rules were passed to, and say that it took them.
     *
     * <p>The one way a reading of a value begins under another. What a case of a sum holds and what
     * a sequence holds are values with declarations of their own, and a clause is not written across
     * either boundary: what {@code Tag} says about itself is written in {@code Tag}, whether the
     * position is reached by narrowing an optional or by being one of however many a list holds. So
     * both cross here, and a shape this compiler learns to walk later is a shape whose rules are
     * read only if it comes through this too.
     *
     * <p>Taking the rules over is said here and not worked out afterwards from the readings that
     * exist. A reading opened under a position for some other reason is not one anybody handed
     * anything to, and letting it discharge the obligation would read the absence of a failure as
     * evidence that something was read (#1072).
     */
    private static void takeTheRulesOver(TermPath by, TermPath at, TermPath opened, Type type,
                                         int depth, Symbols symbols, ReadingPolicy policy,
                                         List<Position> found, List<RuleRoot> roots,
                                         java.util.Set<Type> visited, RuleHandoffs handoffs,
                                         NameReach.Observed observed,
                                         PlacedRules.Reaching crossing,
                                         List<PlacementSeed> account) {
        roots.add(new RuleRoot(opened, type));
        handoffs.accepts(by, at, opened);
        PlacedRules rules = PlacedRules.of(opened, type, symbols, policy, crossing);
        // Said as the reading of this value is opened, so that what a build has to account for is
        // what the rules of the values it read actually placed.
        account.addAll(rules.placed());
        walk(opened, type, depth, symbols, policy, rules, found, roots, visited,
                handoffs, observed, account);
    }

    /**
     * One branch of a position, where the reading still owes it and something stands under it.
     *
     * <p><b>A narrowing takes no level.</b> {@code query@GlobalQuery.limit} is the same distance
     * from the parameter as {@code query.limit} is under a record parameter, because naming which
     * case a value turned out to be does not move into it. Counted as a level, the same field would
     * be measured or not according to whether an author wrote a sum around the record it is in.
     *
     * <p>And the rules under it are the case's. A clause is not written across a narrowing: what a
     * {@code GlobalQuery} says about its {@code tag} is written in {@code GlobalQuery}, so a new
     * root begins here and the reading of the sum's own value has nothing to say below it.
     */
    private static void walkBranch(StructuralInspection.Branch branch, TermPath by, TermPath path,
                                   int depth, Symbols symbols, ReadingPolicy policy,
                                   List<Position> found, List<RuleRoot> roots,
                                   java.util.Set<Type> visited, RuleHandoffs handoffs,
                                   NameReach.Observed observed, PlacedRules.Reaching crossing,
                                   List<PlacementSeed> account) {
        // <b>A descent that costs no level stops only where it returns to a value it has already
        // been at without a step into one.</b> That is the whole of the rule, and what it is keyed
        // on is the value reached and never the narrowing taken: a narrowing is an edge and the
        // thing that has to terminate is a state, and the two agree only where the edge decides the
        // state. A case of a sum does decide it — the case names the type — and whether an optional
        // holds anything does not, so an `Option<Option<Int>>` read on the narrowing would be one
        // `Some` deep for ever after.
        //
        // Kept per branch of the walk and dropped at every step into a value, because a value met
        // under a field is one this walk has been nowhere near.
        //
        // And no reading is opened, so nothing takes the rules of this case over and the handoff
        // above stays standing. The rules were read where the value was first met, at a position
        // this walk already reported; saying they were read here as well would be one reading
        // discharging an obligation raised somewhere it never went.
        if (visited.contains(branch.under())) {
            return;
        }
        java.util.Set<Type> deeper = new java.util.LinkedHashSet<>(visited);
        deeper.add(branch.under());
        takeTheRulesOver(by, path, path.refine(branch.refinement()), branch.under(), depth, symbols,
                policy, found, roots, deeper, handoffs, observed, crossing, account);
    }

    /**
     * Whether the reading of {@code position} still owes a row at this branch.
     *
     * <p>Asked in the words the obligations are in, through the one relating of the two
     * ({@link Refinement#of}). Matched on the kind of distinction here, a branch of a kind this
     * happened not to name would be a branch nothing owes and nothing walks.
     */
    private static boolean owed(Position position, Refinement refinement) {
        for (Case each : position.obligationCases()) {
            if (refinement.equals(Refinement.of(each))) {
                return true;
            }
        }
        return false;
    }

    /** The position's own value, as the reading of one coordinate names it. */
    private static final souther.compiler.check.FieldDomains.CoordinateKind ITS_OWN_VALUE =
            new souther.compiler.check.FieldDomains.CoordinateKind.OfItsOwnValue();

    /** The number {@code operation} answers of what stands at a position. */
    private static souther.compiler.check.FieldDomains.CoordinateKind answeredBy(
            ValueName operation) {
        return new souther.compiler.check.FieldDomains.CoordinateKind
                .OfWhatAnOperationAnswers(operation);
    }

    /**
     * The reading of one position.
     *
     * <p>Which number it is measured at and what its rules leave that number are asked together
     * because they are one reading: whether a rule bounds the length of a string is how it is known
     * that the length is the number being measured.
     */
    private static Position read(ReadablePosition input, TermPath path, Symbols symbols,
                                 PlacedRules placed, StructuralInspection structure,
                                 List<Case> declared) {
        TypeView view = input.view();
        Type type = view.declared();
        Carrier carried = Carrier.ofValue(type, symbols);
        ValueName.Stdlib taken = NumericMeasures.takenOf(type, symbols);
        // The ends the value this sits in places on this position, which its own type says nothing
        // about. Read beside the type's own rules and not after them: a clause naming one coordinate
        // and a constant places an end wherever it is written, so where the rule was written is not
        // what decides whether there is a line here (ADR-0090).
        List<FieldDomains.Placed> stated = placed.placedAt(path);
        // What the rules are about, and only then what the type could carry. A position has one
        // axis, and a `String` is the one type that can be measured two ways — its own order, and
        // the length of it — so which of them the model wrote about is what decides. Read off the
        // carrier first, every rule anybody ever wrote about the length of a string would have
        // become a rule about the string.
        DeclaredBounds.Bounds ofType = taken == null ? null
                : DeclaredBounds.of(type, symbols, Carrier.WHOLE, taken);
        DeclaredBounds.Bounds valueOfType = carried == null ? null
                : DeclaredBounds.of(type, symbols, carried, null);
        // Rules about both coordinates and nothing here to choose between. Said before they are
        // dropped and from the list that still holds them, because this is the one place that knows
        // which rules they were — recovered afterwards from a position with no axis, the finding
        // could name the position and nothing else, which is what it is for.
        List<RuleWithoutALine> competing = List.of();
        if (undecidable(ofType, valueOfType, stated, taken, carried)) {
            competing = competingCoordinates(stated, path, type, symbols);
            stated = List.of();
        }
        boolean bySize = measuredHere(ofType, valueOfType, stated, taken);
        NumericTerm term = bySize ? NumericTerm.TakenOf.of(taken, path, type, symbols)
                : new NumericTerm.ValueOf(path);
        if (term == null) {
            throw new IllegalStateException(
                    "this reading decided " + path + " is measured by " + taken
                            + ", which is not what its type is measured by: " + Type.show(type));
        }
        DeclaredBounds.Bounds own = bySize
                ? DeclaredBounds.and(ofType, DeclaredBounds.placed(stated, answeredBy(taken), Carrier.WHOLE))
                : carried == null ? null
                        : DeclaredBounds.and(valueOfType, DeclaredBounds.placed(stated, ITS_OWN_VALUE, carried));
        // A value whose rules contradict has no positions to cover: every edge of every field of it
        // is a row nobody can write, which is not the same answer as a field nothing bounds.
        boolean nothingExists = placed.bounds().infeasible();
        // Which values the position may hold, and how much of what its rules say was read. The same
        // reading the numbers come from and a separate question of it: a rule can name the values a
        // position holds without stating where they stop, and one that states where they stop
        // without naming any of them.
        AdmissibleSet admitted = placed.admits(path);
        // A record's rule relates the numbers its fields hold, so it reaches the term that is one of
        // them and no other: a cap on a field says nothing about how long the string beside it is.
        NumericDomain.Bounds projected =
                term instanceof NumericTerm.ValueOf ? placed.at(path) : null;
        // Two questions of one pair of readings, and they do not have one answer. What the term's
        // values can be is every rule about it intersected; where it is divided is only where its
        // own type draws a line, because a clause relating two fields is not a partition of one.
        NumericDomain.Bounds admissible = nothingExists ? null
                : TypeBounds.admissible(own, projected, term);
        List<RuleWithoutALine> withoutALine =
                rulesWithoutALineAt(placed, path, type, symbols, competing);

        ReadingResult reading = crossed(declared, view, admissible, admitted, symbols,
                withoutALine,
                nothingExists, type);
        return new ReadPosition(path, view, term, admissible, own, projected,
                // Where the position actually stops, which the ends as written do not say: a clause
                // placing one at 0 beside a clause that takes the 0 away leaves a position whose
                // first value is 1, and a line drawn at the 0 is drawn at no value of it.
                placed.leftAt(path, bySize ? answeredBy(taken) : ITS_OWN_VALUE),
                placed.narrowedBy(path, true), placed.narrowedBy(path, false), nothingExists,
                placed.projection(), declared, reading,
                ObligationDomain.of(reading, declared), admitted.completeness(),
                admitted.whyPartial() == null ? null : Crossing.stopped(admitted.whyPartial()),
                withoutALine,
                // What the rules of this position raise that nothing answered. Asked of the
                // accounting rather than read off the completeness beside it: one reading being
                // short of a position's rules is that reading's business, and a rule another
                // reading took in is not a rule left unread.
                standingAt(placed, path, type, symbols),
                // And whether the rules were reached at all, asked of the gathering that knows.
                // No question is raised where nothing was seen, so an empty list beside it would
                // say every rule was accounted for. Read off the reading's own reason instead, a
                // position carrying both a rule it could not read and a subtree it never entered
                // answered with the first and lost the second.
                //
                // Only this reading's own loss is known here. Whether a handing over was taken up
                // is the descent's to say, and it is added afterwards
                // ({@link #shortOfHandedOnRules}).
                placed.everyRuleReachedAt(path) ? java.util.Set.of()
                        : java.util.Set.of(new RulesLeftUnread.ClauseOfThisReadingWasUnread()),
                structure);
    }

    /**
     * What the position's declarations leave standing.
     *
     * <p>The type's own distinctions crossed with the rules, and where the type states none, the
     * values the rules name. Asked in this order rather than merged: what a type states is what the
     * position's values are, and a rule naming some of them divides what is left rather than
     * replacing it.
     *
     * <p>A type nothing could be read off answers neither, and says so: an empty reading and a
     * reading that could not be made read alike and are not the same claim.
     */
    private static ReadingResult crossed(List<Case> declared, TypeView view,
                                         NumericDomain.Bounds admissible, AdmissibleSet admitted,
                                         Symbols symbols,
                                         List<RuleWithoutALine> withoutALine,
                                         boolean nothingExists, Type type) {
        BlockReason.AboutThePosition unreadable = Distinctions.unreadableAt(view);
        if (unreadable != null) {
            return new ReadingResult.Unsupported(unreadable);
        }
        BlockReason.RuleReadingStopped here = stoppedOn(withoutALine);
        if (!declared.isEmpty()) {
            return Crossing.of(declared, view, admissible, admitted, symbols, here);
        }
        // The values a rule named, where the type states no division. Not crossed with anything:
        // the reading that named them is the reading of the rules, and a value the rules single out
        // is one they admit. Nothing is read for a value whose own rules contradict — there is no
        // value of it for a rule to have named.
        List<Case> named = nothingExists ? List.of()
                : Distinctions.ofValues(admitted.approximation(), type, symbols);
        BlockReason.ReadingStopReason why = admitted.whyPartial() != null
                ? Crossing.stopped(admitted.whyPartial()) : here;
        if (why != null) {
            return new ReadingResult.Partial(named, List.of(), why);
        }
        return admitted.alternativesNotSeparated()
                ? new ReadingResult.NotSeparated(named, List.of())
                : new ReadingResult.Complete(named, List.of());
    }

    /**
     * A rule at this position that this compiler got partway through, or null where there is none.
     *
     * <p>What such a rule costs the reading is everything it would have said, so a position holding
     * one has values this cannot claim are what the rules leave. That is what a caller does with
     * this, and it is why the rules read from end to end are not here: a rule that placed no line
     * because it relates two positions, or because its quantity is empty, was taken in whole and
     * takes nothing back. Handed one of those, the reading called itself partial over a position
     * nothing had been short of, and every claim about its cases came back unsettled because a rule
     * went unread.
     *
     * <p>The first, and the rest say the same thing. Any one of them costs the reading the same —
     * the values are an upper bound and there is no more or less of that — and which rule to go and
     * look at is the finding's to say, one per rule, where they are all named.
     */
    private static BlockReason.RuleReadingStopped stoppedOn(List<RuleWithoutALine> rules) {
        for (RuleWithoutALine each : rules) {
            if (each.why() instanceof BlockReason.RuleReadingStopped stopped) {
                return stopped;
            }
        }
        return null;
    }

    /**
     * Whether this position's one coordinate is the count taken of it rather than its value.
     *
     * <p>The position's own type answers first and its answer stands. A rule reaching the position
     * from the value it sits in states an end on a coordinate; it does not say which coordinate the
     * position is measured at, and letting it say so takes an axis away — {@code data Name = String
     * invariant value >= "m"} held in a record that bounds the length of it would stop being
     * measured on its own order, and the line at `m` would go without anything saying it had.
     *
     * <p>Where the type chose nothing, one of these rules may — and only one, which is what
     * {@link #undecidable} has already refused.
     */
    private static boolean measuredHere(DeclaredBounds.Bounds ofType,
                                        DeclaredBounds.Bounds valueOfType,
                                        List<FieldDomains.Placed> stated, ValueName.Stdlib taken) {
        if (stated(ofType)) {
            return true;
        }
        if (stated(valueOfType)) {
            return false;
        }
        return taken != null && stated(DeclaredBounds.placed(stated, answeredBy(taken), Carrier.WHOLE));
    }

    /**
     * One finding per rule dropped because the position's two coordinates are both spoken for.
     *
     * <p>Per rule and not per position. Both of them were read, both place an end, and neither can
     * be the one the position is measured at — so each is a rule an author would have to rewrite,
     * and telling them the position was short of something leaves them to work out which two of
     * their clauses are in the way. A rule placing two ends is one rule and one finding, which is
     * what the key settles.
     */
    private static List<RuleWithoutALine> competingCoordinates(List<FieldDomains.Placed> stated,
                                                         TermPath path, Type type,
                                                         Symbols symbols) {
        List<RuleWithoutALine> out = new ArrayList<>();
        for (FieldDomains.Placed each : stated) {
            RuleWithoutALine said = new RuleWithoutALine(each.from(),
                    souther.compiler.check.RuleCitation.named(each.from()),
                    // Each rule at the coordinate that rule is about, which is what makes the two
                    // two. What is undecided is which of them the position is measured at, and that
                    // is a fact about the position rather than about either rule — this reading has
                    // chosen no term for the position, and each rule chose one for itself.
                    filedAt(path, each.at(), type, symbols),
                    new BlockReason.CompetingCoordinates());
            if (out.stream().noneMatch(had -> had.sameAs(said))) {
                out.add(said);
            }
        }
        return List.copyOf(out);
    }

    /**
     * The number one rule of a declaration is about, as a finding names it.
     *
     * <p><b>The rule's own answer and not this reading's.</b> Which number a position is measured
     * at and which number a rule is about are two questions, and they coincide only while a
     * position has at most one number taken of it. Answered with the term this reading chose for
     * the position, a rule about one operation's number would be filed at another's the day a
     * second is taken of the same place — which is the identity this coordinate exists to keep.
     *
     * <p>The operation comes from the clause's reading, which recorded it against the count, and
     * the path from this one. Neither can name the term alone: a path is held there as a spelling,
     * and one parsed back out of a spelling is a path this compiler made up.
     *
     * <p>No falling back to the position. A rule with an operation beside it is a rule about that
     * operation's number, so a term that cannot be built from the two is the reading of the clause
     * and the reading of the position disagreeing about what stands here — which is this compiler
     * contradicting itself rather than something the model left out.
     */
    private static FilingCoordinate filedAt(TermPath path,
                                            souther.compiler.check.FieldDomains.Coordinate at,
                                            Type type, Symbols symbols) {
        return FilingCoordinate.of(termAt(path, at, type, symbols));
    }

    /**
     * The number a coordinate of a declaration's own reading names, in this input's vocabulary.
     *
     * <p><b>The one crossing.</b> The operation comes from that reading, which recorded it against
     * the count, and the path from this one — and neither names the term alone: a path is held over
     * there as a key relative to the value the clauses are written on, and one parsed back out of a
     * spelling is a path this compiler made up.
     *
     * <p>Shared by the two things that cross here, a finding about a rule and a question a rule
     * raised, because it is one crossing and not a repetition. Written at each of them, the two
     * would be free to differ by a round of edits, and what they disagreed about would be which
     * number a rule is about.
     *
     * <p><b>One arm per kind of coordinate, and no falling back to the position.</b> A coordinate
     * this does not classify is not one measured by its own values; written as a test for the
     * operation with the position as the other answer, a kind added later would arrive here as a
     * term about something the model never wrote, and the reading of it would be applied to
     * whatever stood at the path.
     */
    private static NumericTerm termAt(TermPath path,
                                      souther.compiler.check.FieldDomains.Coordinate at,
                                      Type type, Symbols symbols) {
        return switch (at.kind()) {
            case souther.compiler.check.FieldDomains.CoordinateKind.OfItsOwnValue _ ->
                    new NumericTerm.ValueOf(path);
            case souther.compiler.check.FieldDomains.CoordinateKind
                    .OfWhatAnOperationAnswers answered -> takenBy(answered.operation(), path, type,
                            symbols);
        };
    }

    /**
     * The term for what {@code by} answers of what stands at {@code path}.
     *
     * <p>Both refusals are this compiler contradicting itself rather than something the model left
     * out, which is why neither is an answer a caller can act on.
     */
    private static NumericTerm takenBy(ValueName by, TermPath path, Type type, Symbols symbols) {
        // The operation a count is taken by is one the library declares, which is what the reading
        // that recorded the count went to. Anything else here is that reading and this one holding
        // different ideas of what an operation is.
        if (!(by instanceof ValueName.Stdlib operation)) {
            throw new IllegalStateException("a clause of `" + path + "` was read as a rule about `"
                    + by + "`, which is not an operation a number is taken by");
        }
        NumericTerm.TakenOf taken = NumericTerm.TakenOf.of(operation, path, type, symbols);
        if (taken == null) {
            throw new IllegalStateException("a clause of `" + path + "` was read as a rule about `"
                    + by + "`, and that takes no number of what stands there");
        }
        return taken;
    }

    /**
     * The questions the rules of this position raise that nothing answered, crossed into this
     * input's vocabulary.
     *
     * <p>Here, where the root the walk started at and the type standing at the position both are.
     * The reading that raised them knows its positions by a key relative to the value its clauses
     * are written on and knows a number of one by the operation beside that key; what everything
     * past here compares is a term path and a term.
     */
    private static List<StandingQuestion> standingAt(PlacedRules placed, TermPath path, Type type,
                                                     Symbols symbols) {
        List<StandingQuestion> out = new ArrayList<>();
        for (souther.compiler.check.RuleAccounting.Unanswered each : placed.unanswered(path)) {
            out.add(new StandingQuestion(each.rule(), each.cited(),
                    switch (each.owed()) {
                        case souther.compiler.check.Owed.AdmittedValues _ ->
                                new InputQuestion.AboutAPosition(path);
                        case souther.compiler.check.Owed.Boundary it ->
                                new InputQuestion.AboutANumber(
                                        termAt(path, it.on(), type, symbols));
                    }));
        }
        return List.copyOf(out);
    }

    /**
     * Whether the rules reaching this position say where both of its coordinates stop, with its own
     * type having said nothing about either.
     *
     * <p>A position has one coordinate and this is the one case with no answer. Which of a
     * {@code String}'s two a rule is about is settled by which one the model wrote about, and here
     * the model wrote about both from outside. Choosing either would put a line the author can read
     * beside one they cannot see, so the position is left as one nothing divides and both rules go
     * unread — the coarser of the two things that could be said, and the one that claims nothing.
     */
    private static boolean undecidable(DeclaredBounds.Bounds ofType,
                                       DeclaredBounds.Bounds valueOfType,
                                       List<FieldDomains.Placed> stated, ValueName.Stdlib taken,
                                       Carrier carried) {
        return !stated(ofType) && !stated(valueOfType)
                && taken != null && carried != null
                && stated(DeclaredBounds.placed(stated, answeredBy(taken), Carrier.WHOLE))
                && stated(DeclaredBounds.placed(stated, ITS_OWN_VALUE, carried));
    }

    private static boolean stated(DeclaredBounds.Bounds bounds) {
        return bounds != null && !bounds.isEmpty();
    }

    /**
     * The rules saying where this position's values stop that nothing turned into an end.
     *
     * <p>The invariant's half of what a {@code guard}'s comparison is asked. Both draw lines
     * (ADR-0090) and both can be written in a form this does not read, and only one of them was
     * saying so — a bound it dropped left the position looking like one no rule bounds, which is
     * what the declaration above it denies.
     *
     * <p>Read off the one reading that draws lines from clauses ({@link FieldDomains#noLineAt}) and
     * not walked again here. A second walk over the position's own type answered for the clauses
     * written on it and knew nothing of the clauses written on the value it sits in, so a record's
     * rule about one of its fields was dropped in silence; and where both had something to say
     * about one clause, the report printed two causes for it.
     *
     * <p>One finding per rule, as a {@code guard}'s comparison is. Two clauses stopped by the same
     * limit at one position are two things for a reader to lift and are two findings: which clause
     * to rewrite is what an author acts on, and a position is not it. Kept per reason, the second
     * of them was dropped as a repeat of the first.
     */
    private static List<RuleWithoutALine> rulesWithoutALineAt(PlacedRules placed, TermPath path, Type type,
                                                  Symbols symbols, List<RuleWithoutALine> competing) {
        List<RuleWithoutALine> out = new ArrayList<>(competing);
        for (FieldDomains.NoLine each : placed.noLineAt(path)) {
            // The rule the reading of ends was holding when it gave up, carried rather than left
            // behind. It is a clause of an invariant, so it has a name and the handle is that name.
            //
            // At the number that rule is about, which the rule itself says. Nothing is missing here
            // for the position to stand in for: a clause was read far enough to be about one number
            // or the other, and it is only the line that nothing came of.
            RuleWithoutALine said = new RuleWithoutALine(each.from(),
                    souther.compiler.check.RuleCitation.named(each.from()),
                    filedAt(path, each.at(), type, symbols),
                    each.why());
            if (out.stream().noneMatch(had -> had.sameAs(said))) {
                out.add(said);
            }
        }
        return List.copyOf(out);
    }
}
