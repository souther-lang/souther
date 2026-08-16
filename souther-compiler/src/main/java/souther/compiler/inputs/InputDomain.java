package souther.compiler.inputs;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.HelperInvariants;
import souther.compiler.check.InvariantBound;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.numeric.NumericDomain;
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
    public static final InputDomain NONE = new InputDomain(List.of());

    private final List<Position> positions;
    private final Map<TermPath, Position> byPath;

    private InputDomain(List<Position> positions) {
        this.positions = List.copyOf(positions);
        Map<TermPath, Position> at = new LinkedHashMap<>();
        // The first reading of a path stands. A path is where a rule and a row meet, so two
        // readings under one path would be the position answering differently depending on which
        // reader looked it up.
        positions.forEach(each -> at.putIfAbsent(each.path(), each));
        this.byPath = Map.copyOf(at);
    }

    /** One thing a behavior is applied to: what it is called, and what it holds. Taken together
     *  because they are one fact — a name beside a type is a pair a caller can get out of step. */
    public record Parameter(String name, Type type) {}

    /** Every position of an input, in the order the parameters are declared and descended into. */
    public static InputDomain of(List<Parameter> parameters, Symbols symbols) {
        List<Position> found = new ArrayList<>();
        for (Parameter parameter : parameters) {
            walk(TermPath.of(parameter.name()), parameter.type(), 0, symbols,
                    PlacedRules.of(parameter.type(), symbols), found);
        }
        return found.isEmpty() ? NONE : new InputDomain(found);
    }

    /**
     * The same, of a behavior.
     *
     * <p>The one place a name and a type are put side by side: the declaration says what the
     * parameters are called and the signature says what they hold, and the pairing is done here
     * rather than by every caller that has both.
     */
    public static InputDomain of(Hir.SpecBehavior behavior, Sig sig, Symbols symbols) {
        List<Parameter> parameters = new ArrayList<>();
        for (int i = 0; i < sig.inputTypes().size() && i < behavior.params().size(); i++) {
            parameters.add(new Parameter(behavior.params().get(i).name(), sig.inputTypes().get(i)));
        }
        return of(parameters, symbols);
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
                unread, structure);
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
                for (Hir.Expr each : HelperInvariants.conjunctsOf(clause.expr())) {
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
            return InvariantBound.of(clause, carried).isPresent()
                    ? null : new BlockReason.UnreadComparisonForm();
        }
        if (measure != null && InvariantBound.statesAnEnd(clause, measure)) {
            // A size is a whole number whatever it is a size of, so nothing here is about a carrier.
            return InvariantBound.ofSize(clause, measure).isPresent() ? null
                    : new BlockReason.UnreadComparisonForm();
        }
        return null;
    }
}
