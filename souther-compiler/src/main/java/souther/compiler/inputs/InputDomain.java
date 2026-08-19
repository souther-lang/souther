package souther.compiler.inputs;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.ClauseHelpers;
import souther.compiler.check.InvariantBound;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
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
 * <p>Nothing a body writes reaches this. A {@code guard}'s line, a {@code match} arm and an
 * {@code unreachable} are statements about the same positions and are read against this rather than
 * into it — which is what keeps a body from moving the denominator it is measured by.
 */
public final class InputDomain {

    /** How deep a product is taken apart. Two levels reach a field of a record a parameter holds,
     * which is where domain rules are written; below that a report stops being about anything the
     * author would recognise as one input. */
    public static final int MAX_DEPTH = 2;

    /** Nothing to read: a behavior whose signature is not in hand. */
    public static final InputDomain NONE = new InputDomain(List.of(), Map.of());

    private final List<Position> positions;
    private final Map<TermPath, Position> byPath;
    private final Map<BindingId, String> read;

    private InputDomain(List<Position> positions, Map<BindingId, String> read) {
        this.positions = List.copyOf(positions);
        this.read = Map.copyOf(read);
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
    public static InputDomain of(List<Parameter> parameters, Symbols symbols) {
        List<Position> found = new ArrayList<>();
        Map<BindingId, String> read = new LinkedHashMap<>();
        for (Parameter parameter : parameters) {
            if (parameter.binding() != null) {
                read.putIfAbsent(parameter.binding(), parameter.name());
            }
            walk(TermPath.of(parameter.name()), parameter.type(), 0, symbols,
                    PlacedRules.of(parameter.type(), symbols), found);
        }
        return found.isEmpty() ? NONE : new InputDomain(found, read);
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
                                 Symbols symbols) {
        List<Parameter> parameters = new ArrayList<>();
        for (int i = 0; i < sig.inputTypes().size() && i < behavior.params().size(); i++) {
            BindingId binding = fn != null && i < fn.params().size()
                    ? fn.params().get(i).binder().binding() : null;
            parameters.add(new Parameter(behavior.params().get(i).name(), binding,
                    sig.inputTypes().get(i)));
        }
        return of(parameters, symbols);
    }

    /**
     * The same, of an input nothing reads a body against.
     *
     * <p>The positions are the same either way — what a behavior takes is what it declares — and
     * what is absent is the means to tell one of its parameters from a name a body binds under the
     * same spelling. So this is the reading for a caller with no body in hand, and a caller with one
     * that used it would find every claim and every comparison naming nothing.
     */
    public static InputDomain of(Hir.SpecBehavior behavior, Sig sig, Symbols symbols) {
        return of(behavior, null, sig, symbols);
    }

    /** The positions, in the order they were read. */
    public List<Position> positions() {
        return positions;
    }

    /** The position at {@code path}, or null where the input has none there — a path below where
     *  the walk stops, or one that is not a position of this behavior at all. */
    public Position at(TermPath path) {
        return byPath.get(path);
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
     * One position, read, and then what is under it.
     *
     * <p>What is under a position is walked whether or not the position itself came to anything.
     * Only a product has children, and a product states no distinction of its own and carries no
     * end, so nothing is read here that a reader would have to weigh against the position above
     * it — and a reader that gives a position up in favour of its fields finds them read either
     * way.
     */
    private static void walk(TermPath path, Type type, int depth, Symbols symbols,
                             PlacedRules placed, List<Position> found) {
        // The proof first, and before anything is read off the position. A shape a reading is not
        // made of is this compiler disagreeing with itself about what may stand at a position, and
        // it is refused here rather than arriving further down as a position nothing divides.
        ReadablePosition input = ReadablePosition.of(TypeView.of(type, symbols));
        StructuralInspection structure =
                StructuralInspection.of(input.shape(), depth < MAX_DEPTH);
        found.add(read(input, path, symbols, placed, structure));
        if (structure instanceof StructuralInspection.Children children) {
            for (Map.Entry<String, Type> field : children.under().entrySet()) {
                walk(path.then(field.getKey()), field.getValue(), depth + 1, symbols, placed, found);
            }
        }
    }

    /**
     * The reading of one position.
     *
     * <p>Which number it is measured at and what its rules leave that number are asked together
     * because they are one reading: whether a rule bounds the length of a string is how it is known
     * that the length is the number being measured.
     */
    private static Position read(ReadablePosition input, TermPath path, Symbols symbols,
                                 PlacedRules placed, StructuralInspection structure) {
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
        if (undecidable(ofType, valueOfType, stated, taken, carried)) {
            stated = List.of();   // rules about both coordinates and nothing here to choose between
        }
        boolean bySize = measuredHere(ofType, valueOfType, stated, taken);
        NumericTerm term = bySize ? new NumericTerm.SizeOf(taken, path) : new NumericTerm.ValueOf(path);
        DeclaredBounds.Bounds own = bySize
                ? DeclaredBounds.and(ofType, DeclaredBounds.placed(stated, true, Carrier.WHOLE))
                : carried == null ? null
                        : DeclaredBounds.and(valueOfType, DeclaredBounds.placed(stated, false, carried));
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
        List<UnreadRule> unread = unreadBoundsAt(path, type, symbols, carried, taken);

        List<Case> declared = Distinctions.ofType(view, symbols);
        ReadingResult reading = crossed(declared, view, admissible, admitted, symbols, unread,
                nothingExists, type);
        return new ReadPosition(path, view, term, admissible, own, projected,
                placed.narrowedBy(path, true), placed.narrowedBy(path, false), nothingExists,
                placed.bounds().allRulesRead(), declared, reading,
                ObligationDomain.of(reading, declared), admitted.completeness(),
                admitted.whyPartial() == null ? null : Crossing.stopped(admitted.whyPartial()),
                unread,
                // What the rules of this position raise that nothing answered. Asked of the
                // accounting rather than read off the completeness beside it: one reading being
                // short of a position's rules is that reading's business, and a rule another
                // reading took in is not a rule left unread.
                placed.unanswered(path),
                // And whether the rules were reached at all, asked of the gathering that knows.
                // No question is raised where nothing was seen, so an empty list beside it would
                // say every rule was accounted for. Read off the reading's own reason instead, a
                // position carrying both a rule it could not read and a subtree it never entered
                // answered with the first and lost the second.
                !placed.everyRuleReachedAt(path),
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
                                         Symbols symbols, List<UnreadRule> unread,
                                         boolean nothingExists, Type type) {
        BlockReason unreadable = Distinctions.unreadableAt(view);
        if (unreadable != null) {
            return new ReadingResult.Unsupported(unreadable);
        }
        BlockReason here = unread.isEmpty() ? null : unread.get(0).why();
        if (!declared.isEmpty()) {
            return Crossing.of(declared, view, admissible, admitted, symbols, here);
        }
        // The values a rule named, where the type states no division. Not crossed with anything:
        // the reading that named them is the reading of the rules, and a value the rules single out
        // is one they admit. Nothing is read for a value whose own rules contradict — there is no
        // value of it for a rule to have named.
        List<Case> named = nothingExists ? List.of()
                : Distinctions.ofValues(admitted.approximation(), type, symbols);
        BlockReason why = admitted.whyPartial() != null ? Crossing.stopped(admitted.whyPartial())
                : here;
        return why == null ? new ReadingResult.Complete(named, List.of())
                : new ReadingResult.Partial(named, List.of(), why);
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
        return taken != null && stated(DeclaredBounds.placed(stated, true, Carrier.WHOLE));
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
                && stated(DeclaredBounds.placed(stated, true, Carrier.WHOLE))
                && stated(DeclaredBounds.placed(stated, false, carried));
    }

    private static boolean stated(DeclaredBounds.Bounds bounds) {
        return bounds != null && !bounds.isEmpty();
    }

    /**
     * The rules on this position's own type that say where its value stops and that nothing here
     * turned into an end.
     *
     * <p>The invariant's half of what a {@code guard}'s comparison is asked. Both draw lines
     * (ADR-0090) and both can be written in a form this does not read, and only one of them was
     * saying so — a bound it dropped left the position looking like one no rule bounds, which is
     * what the declaration above it denies.
     *
     * @param carried what the value is read on, or null where nothing here draws a line on it
     * @param measure the operation a number is taken by, or null where none is
     */
    private static List<UnreadRule> unreadBoundsAt(TermPath path, Type type, Symbols symbols,
                                                   Carrier carried, ValueName measure) {
        List<UnreadRule> out = new ArrayList<>();
        for (TypeOps.Layer layer : TypeOps.newtypeChain(type, symbols)) {
            for (Hir.InvariantClause clause : TypeOps.effectiveInvariants(layer.data(), symbols)) {
                for (Hir.Expr each : ClauseHelpers.conjunctsOf(clause.expr())) {
                    BlockReason why = whyUnread(each, carried, measure);
                    // Once per position, as a comparison is: what a reader has to lift is the first
                    // limit in the way, and a second clause behind it says nothing further.
                    if (why != null && out.isEmpty()) {
                        out.add(new UnreadRule(path, why));
                    }
                }
            }
        }
        return List.copyOf(out);
    }

    /** What stopped one clause from being an end, or null where nothing did — either because it was
     * read, or because it is not a rule about where the value stops. */
    private static BlockReason whyUnread(Hir.Expr clause, Carrier carried, ValueName measure) {
        if (InvariantBound.statesAnEnd(clause, null)) {
            if (carried == null) {
                // The value is ordered — it is compared in the clause — and this reads no line on
                // what carries it. The carrier, asked of the carrier, as a guard's is.
                return new BlockReason.UnreadComparisonDomain();
            }
            return unreadFormOf(InvariantBound.of(clause, carried), true);
        }
        if (measure != null && InvariantBound.statesAnEnd(clause, measure)) {
            // A size is a whole number whatever it is a size of, so nothing here is about a carrier.
            // And nothing takes a size's ends into the reading that refuses a declaration for
            // holding no value: that reading is over the positions a value has, and a size is a
            // number taken of one. So a size bound past the end of the whole numbers is a rule this
            // report is the only reader of, and going quiet about it would leave it unsaid
            // everywhere.
            return unreadFormOf(InvariantBound.ofSize(clause, measure), false);
        }
        return null;
    }

    /**
     * What a reading of an ordered rule leaves for the report to say about it.
     *
     * <p>Nothing where an end was read. A rule stating an end past the last value of the order is
     * the case the two callers differ on, and what settles it is whether anything else says
     * something about such a rule: where the declaration is refused for holding no value, this
     * report is never produced and naming the rule as one nothing could read would send an author
     * after a bound the compiler understood perfectly; where nothing refuses it, this is its only
     * reader and silence is the rule going unsaid.
     *
     * @param refusedElsewhere whether a rule stating an end past the end of the order is taken into
     *                         the reading that refuses a declaration for holding no value
     */
    private static BlockReason unreadFormOf(InvariantBound.Read read, boolean refusedElsewhere) {
        return switch (read) {
            case InvariantBound.Read.AnEnd _ -> null;
            case InvariantBound.Read.PastWhereTheOrderStops _ ->
                    refusedElsewhere ? null : new BlockReason.UnreadComparisonForm();
            case InvariantBound.Read.NoEnd _ -> new BlockReason.UnreadComparisonForm();
        };
    }
}
