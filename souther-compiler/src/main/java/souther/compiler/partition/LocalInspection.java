package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.HelperInvariants;
import souther.compiler.check.InvariantBound;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.UnreadReason;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A position read once, and what that reading came to.
 *
 * <p>The two are separate and travel together, which is the whole of what keeps the answer honest.
 * {@link LocalReading} is what the position was seen to be — its term, what its rules leave its
 * numbers and its values, what could not be read. {@link LocalPartition} is what follows from it.
 * Held as one value, a conclusion could carry a reading that says the opposite of it, and the
 * discipline stopping that would be a rule somebody has to remember at each place one is built.
 *
 * <p>So the derivation is one way: a reading is completed, and the answer is derived from it. That
 * is what {@link LocalPartition.Open} means and how it is held — {@code Open} has nothing of its
 * own to contradict a reading with, and there is no way to pair one with a reading that did not run
 * to the end, because there is no way to make one of these except by deriving it.
 */
public final class LocalInspection {

    private final LocalReading reading;
    private final LocalPartition partition;

    /**
     * Reached through {@link #of} and nowhere else.
     *
     * <p>Which is the whole of the claim above. A pair carrying a conclusion its reading does not
     * support — an open position off a reading short of the rules, classes said to be read in full
     * off one that was not — is not refused when somebody writes it; there is nowhere to write it.
     * The derivation reads the position and answers about it in one place, and a fourth thing to
     * read is a change to that place rather than a caller to be held to a rule.
     *
     * <p>The alternative was a public constructor checking that the two agree. It says the same
     * thing where it fires, and it says it to a caller who has already made the pair — which is the
     * shape this protocol was rebuilt to stop needing.
     */
    private LocalInspection(LocalReading reading, LocalPartition partition) {
        this.reading = reading;
        this.partition = partition;
    }

    /** What the position was read as, which is the same whichever answer follows. */
    public LocalReading reading() {
        return reading;
    }

    /** What that reading came to. */
    public LocalPartition partition() {
        return partition;
    }

    /**
     * The one reading.
     *
     * <p>Takes the proof rather than the reading. A position outside what a partition may be
     * derived from cannot be handed to this — which is the point of {@link PartitionInput}, and was
     * not true of it while the walk asked for the proof only after this had answered: a shape the
     * boundary should have refused arrived here, produced classes, and never reached the check that
     * exists to make that disagreement loud.
     *
     * @param input  the position, proved to be one a partition may be derived from
     * @param path   where the position sits, which a term is named by
     * @param placed the value the position is inside, or null where it is a parameter itself
     */
    public static LocalInspection of(PartitionInput input, TermPath path, Symbols symbols,
                                     Partitions.Placed placed) {
        TypeView view = input.view();
        Type type = view.declared();
        // Which number this position is measured at, and what its rules leave that number. Asked
        // together because they are one reading: whether a rule bounds the length of a string is how
        // it is known that the length is the number being measured.
        Carrier carried = Carrier.ofValue(type, symbols);
        ValueName.Stdlib taken = NumericMeasures.takenOf(type, symbols);
        // The ends the value this sits in places on this position, which its own type says nothing
        // about. Read beside the type's own rules and not after them: a clause naming one coordinate
        // and a constant places an end wherever it is written, so where the rule was written is not
        // what decides whether there is a line here (ADR-0090).
        List<souther.compiler.check.FieldDomains.Placed> stated =
                placed == null ? List.of() : placed.placedAt(path);
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
        boolean bySize = measuredHere(ofType, valueOfType, stated, taken, carried);
        NumericTerm term = bySize ? new NumericTerm.SizeOf(taken, path) : new NumericTerm.ValueOf(path);
        DeclaredBounds.Bounds own = bySize
                ? DeclaredBounds.and(ofType, DeclaredBounds.placed(stated, true, Carrier.WHOLE))
                : carried == null ? null
                : DeclaredBounds.and(valueOfType, DeclaredBounds.placed(stated, false, carried));
        // A value whose rules contradict has no positions to cover: every edge of every field of it
        // is a row nobody can write, which is not the same answer as a field nothing bounds.
        boolean nothingExists = placed != null && placed.bounds().infeasible();
        // Which values the position may hold, and how much of what its rules say was read. The same
        // reading the numbers come from and a separate question of it: a rule can name the values a
        // position holds without stating where they stop, and one that states where they stop
        // without naming any of them.
        AdmissibleSet admitted = placed == null
                ? AdmissibleSet.complete(ValueSet.ANY) : placed.admits(path);
        // A record's rule relates the numbers its fields hold, so it reaches the term that is one of
        // them and no other: a cap on a field says nothing about how long the string beside it is.
        NumericDomain.Bounds projected = placed == null || !(term instanceof NumericTerm.ValueOf)
                ? null : placed.at(path);
        // Two questions of one pair of readings, and they do not have one answer. What the term's
        // values can be is every rule about it intersected; where it is divided is only where its own
        // type draws a line, because a clause relating two fields is not a partition of one of them.
        NumericDomain.Bounds admissible = nothingExists ? null
                : TypeBounds.admissible(own, projected, term);
        LocalReading reading = new LocalReading(term, admissible, admitted,
                unreadBoundsAt(path, type, symbols, carried, taken));

        // What the type declares, crossed with what the position can hold. Neither reading is the
        // other's input: a case the rules refuse is still a case of the type, and it is here that
        // it stops being a class of this position.
        List<PartitionClass> declared = constructibleAt(PartitionClasses.of(view, symbols), view,
                admissible, admitted, symbols);
        // And where the type states none, the values its rules name. Asked in this order rather
        // than merged: what a type declares is what the position's values are, and a rule naming
        // some of them divides what is left rather than replacing it — which is a narrowing, and is
        // where the declared classes are narrowed rather than a second set of classes.
        List<PartitionClass> classes = nothingExists || !declared.isEmpty() ? declared
                : ValueClasses.of(admitted.approximation(), view, symbols);
        DeclaredBounds.Bounds axis = nothingExists ? null : axisBounds(own, projected);
        List<Cut> cuts = nothingExists ? List.of()
                : cutsOf(type, axis, own,
                        placed == null ? List.of() : placed.narrowedBy(path, true),
                        placed == null ? List.of() : placed.narrowedBy(path, false));
        if (classes.isEmpty() && cuts.isEmpty()) {
            // Nothing divides the position, and what may be concluded from that is what the reading
            // knows about itself. A set of values arrived at from part of the rules names no
            // division; a rule that went unread can divide the position as easily as one that was
            // read, so an absence does not follow from this reading having found none.
            return new LocalInspection(reading, admitted.whyPartial() == null
                    ? new LocalPartition.Open()
                    : new LocalPartition.Blocked(stopped(admitted.whyPartial())));
        }
        // Whether a row can be written at an edge is a question about the whole value the position
        // sits in, so it is answered once for the parameter. A rule this could not read is a way that
        // value can be refused, wherever in it the rule is written.
        CutEvidence drawn = cuts.isEmpty() ? new CutEvidence.None()
                : new CutEvidence.Present(cuts,
                        placed != null && !placed.bounds().allRulesRead());
        return new LocalInspection(reading,
                new LocalPartition.Divided(classes, drawn, admitted.completeness()));
    }

    /**
     * What stopped the values reading, in the vocabulary a report is projected from.
     *
     * <p>A relation between two positions is what {@link BlockReason.ComparisonBetweenPositions}
     * already says, whichever rule wrote it: a {@code guard} comparing two inputs and an
     * {@code invariant} relating two fields leave a reader the same thing to know. The other two
     * are their own, because what would lift each is different work — one wants a reader for a form,
     * and one wants the gathering to reach further.
     */
    private static BlockReason stopped(UnreadReason why) {
        return switch (why) {
            case RELATES_TWO_POSITIONS -> new BlockReason.ComparisonBetweenPositions();
            case FORM_NOT_READ, ALTERNATIVE_NOT_READ -> new BlockReason.UnreadValueRule();
            case NOT_REACHED -> new BlockReason.ValueRulesNotReached();
        };
    }

    /**
     * Whether this position's one coordinate is the count taken of it rather than its value.
     *
     * <p>The position's own type answers first and its answer stands. A rule reaching the position
     * from the value it sits in states an end on a coordinate; it does not say which coordinate the
     * position is measured at, and letting it say so takes an axis away — {@code data Name = String
     * invariant value >= "m"} held in a record that bounds the length of it would stop being measured
     * on its own order, and the line at `m` would go without anything saying it had.
     *
     * <p>Where the type chose nothing, one of these rules may — and only one, which is what
     * {@link #undecidable} has already refused.
     */
    private static boolean measuredHere(DeclaredBounds.Bounds ofType, DeclaredBounds.Bounds valueOfType,
                                        List<souther.compiler.check.FieldDomains.Placed> stated,
                                        ValueName.Stdlib taken, Carrier carried) {
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
     *
     * <p>Which of them a position holds is a question this does not answer, rather than one it
     * answers badly: a position carrying both coordinates is what would settle it, and that is not
     * here (ADR-0090).
     */
    private static boolean undecidable(DeclaredBounds.Bounds ofType, DeclaredBounds.Bounds valueOfType,
                                       List<souther.compiler.check.FieldDomains.Placed> stated,
                                       ValueName.Stdlib taken, Carrier carried) {
        return !stated(ofType) && !stated(valueOfType)
                && taken != null && carried != null
                && stated(DeclaredBounds.placed(stated, true, Carrier.WHOLE))
                && stated(DeclaredBounds.placed(stated, false, carried));
    }

    private static boolean stated(DeclaredBounds.Bounds bounds) {
        return bounds != null && !bounds.isEmpty();
    }

    /**
     * The classes of {@code declared} the position can hold a value of.
     *
     * <p>Two facts crossed, and they are separate facts. That a type declares a case is read off
     * the declaration; that a value of it can stand at <em>this</em> position is what the rules on
     * the position leave. A {@code data StageI = Stage invariant value >= Qualified} declares three
     * cases and holds two of them: {@code StageI(Prospecting)} is refused at construction (E1903)
     * by the same rule, so a class for it is a row nobody can write.
     *
     * <p>Crossed here rather than by handing the bounds to the reading that produces them. Each of
     * the two is a function of the position and neither is a function of the other, so nothing
     * depends on which is worked out first — and a producer that took the other's output would grow
     * a dependency that only shows up as an admissible case coming back when someone tidies the
     * order.
     *
     * <p>Dropped rather than kept and marked. What a body declines to answer for is still a class
     * of the position's values and is reported as excluded ({@link Axis#excluding}); a case the
     * position cannot hold is not one of its values at all, and the classes of an axis are over the
     * values it has.
     *
     * <p>Against both readings of what the position can hold, since a rule reaches whichever of
     * them has a word for it. {@code value >= Qualified} is an interval and {@code value ==
     * Qualified} is a set of values, and the two say the same thing about the same position — read
     * against the intervals alone, the first took two cases away and the second left all three, so
     * which cases a report asked for turned on how the author spelled one rule.
     *
     * @param within what the rules on the position leave its values, or null where nothing bounds
     *               them
     */
    private static List<PartitionClass> constructibleAt(List<PartitionClass> declared, TypeView view,
                                                        NumericDomain.Bounds within,
                                                        AdmissibleSet admitted, Symbols symbols) {
        List<PartitionClass> left =
                admits(constructibleWithin(declared, view, within, symbols), admitted);
        // Nothing left is not a position with no classes. The classes are exhaustive over the
        // type's values, so a position that can hold none of them holds no value at all — a
        // declaration nothing can construct, which is refused where it is written (E1013) and is a
        // rule this compiler does not yet reach in every domain (issue #780). Read as an empty
        // partition it comes back as a position the model divides no way, which is the sentence
        // this reading exists to stop; and it would leave a position whose type states classes
        // without any, which is the state every reader after this one takes as licence to supply
        // its own.
        //
        // Said once for the whole crossing rather than in either reading. Both narrow the same
        // classes for the same reason, and a guard in one of them is a rule that holds depending on
        // which reading happened to refuse the last case.
        return left.isEmpty() ? declared : left;
    }

    /**
     * The classes of {@code declared} left by the values the rules admit.
     *
     * <p>One rule: a class is dropped where the rules leave it nothing. Each class is asked, since
     * knowing what a class holds is what settles it — a finite set proves a class empty by holding
     * no value of it, and a set written as a denial proves it by excluding every value the class
     * has, which a class that is one value can say and a class holding a record cannot
     * ({@link PartitionClass#leftAnythingBy}).
     *
     * <p>Sound whether or not the reading ran to the end of the rules: the set is an upper bound in
     * either case, so a class the rules leave nothing is a class this position cannot hold. A set
     * read in part makes classes as readily as one read whole — the values the model singled out
     * are the same values — and what the completeness beside it decides is what may be said about
     * the classes afterwards, not whether there are any.
     *
     * <p>Only where the classes and the set are about the same values. A value none of the classes
     * holds is the two readings disagreeing about what stands at this position, and the classes are
     * the position's own: taking them away on the strength of a set that does not fit them would
     * leave a position with no classes because two readings of it did not line up.
     */
    private static List<PartitionClass> admits(List<PartitionClass> declared,
                                               AdmissibleSet admitted) {
        if (declared.isEmpty() || admitted.approximation().isAny()) {
            return declared;
        }
        if (admitted.approximation() instanceof ValueSet.Finite finite
                && !finite.values().isEmpty() && finite.values().stream()
                        .anyMatch(value -> declared.stream().noneMatch(each -> holds(each, value)))) {
            return declared;   // the two readings are not about the same values
        }
        return declared.stream()
                .filter(each -> each.leftAnythingBy(admitted.approximation(),
                        value -> holds(each, value)))
                .toList();
    }

    /** Whether a class holds one value, asked of the class. A reading that matched what a class is
     *  called would be a second copy of how a class is named. */
    private static boolean holds(PartitionClass each, Value value) {
        return each.classifier().membershipOf(ValueClasses.observed(value)) == Membership.MATCH;
    }

    /** The same, against what the intervals leave. */
    private static List<PartitionClass> constructibleWithin(List<PartitionClass> declared,
                                                            TypeView view,
                                                            NumericDomain.Bounds within,
                                                            Symbols symbols) {
        if (within == null || declared.isEmpty()
                || !(Carrier.ofValue(view.declared(), symbols) instanceof Carrier.Ordinal order)) {
            return declared;   // no order for a rule to name a value on, so nothing is taken away
        }
        Set<String> refused = new LinkedHashSet<>();
        for (TypeSymbol each : order.cases()) {
            Place at = order.at(each);
            if (at != null && !within.admits(at)) {
                refused.add(PartitionClasses.idOfCase(each));
            }
        }
        return refused.isEmpty() ? declared
                : declared.stream().filter(each -> !refused.contains(each.id())).toList();
    }

    /**
     * The rules on this position's own type that say where its value stops and that nothing here
     * turned into an end.
     *
     * <p>The invariant's half of what a {@code guard}'s comparison is asked in {@link
     * GuardThresholds#comparedIn}. Both draw lines (ADR-0090) and both can be written in a form this
     * does not read, and only one of them was saying so — a bound it dropped left the position
     * looking like one no rule bounds, which is what the declaration above it denies.
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

    /**
     * Where the position is divided: the type's own bound, taken in to where the record it sits in
     * stops.
     *
     * <p>Only taken in. A record's rule moves an edge the type already has; it does not put one on a
     * position the type left open. An {@code Int} nobody bounded stays a position the model draws no
     * line through, which is what a report says of it (ADR-0090) — giving it an edge here would make
     * a rule relating two fields into a partition of one of them.
     *
     * <p>So this is not what the position can hold, and reading it as that is how a cap written on
     * the record alone became invisible: see {@link TypeBounds#admissible}.
     */
    private static DeclaredBounds.Bounds axisBounds(DeclaredBounds.Bounds own,
                                                NumericDomain.Bounds projected) {
        if (own == null || projected == null) {
            return own;
        }
        // The value moves and the names do not: a record narrowing an edge does not take it away
        // from the rule that put one there, and which record did the narrowing is said beside it.
        return new DeclaredBounds.Bounds(
                own.min() == null ? null
                        : new DeclaredBounds.End(Endpoint.lower(own.min().at(), projected.min()),
                                own.min().from()),
                own.max() == null ? null
                        : new DeclaredBounds.End(Endpoint.upper(own.max().at(), projected.max()),
                                own.max().from()),
                own.carrier());
    }

    /**
     * The cuts of a position whose range is already settled.
     *
     * @param bounds where the position stops, the record it sits in taken into account
     * @param own    where its own type stops, so that an end the record moved can say so
     * @param under  the declarations holding the lower end, and {@code over} those holding the
     *               upper. Per end because they are separate answers: one declaration can be holding
     *               a minimum while another holds the maximum, and one slot for both names the wrong
     *               one for at least one of them
     */
    private static List<Cut> cutsOf(Type type, DeclaredBounds.Bounds bounds, DeclaredBounds.Bounds own,
                                    List<TypeSymbol> under, List<TypeSymbol> over) {
        // Nothing about the shape of the position's type. An end is here because some clause placed
        // it, and a clause naming a field of a record places one on a bare `Int` and on the length of
        // a bare `List<Int>` as readily as on a newtype over either. Asking for a `Type.Ref` here was
        // reading the one route an end could arrive by as the condition for having one.
        if (bounds == null || bounds.isEmpty()) {
            return List.of();
        }
        Map<String, Cut> byValue = new LinkedHashMap<>();
        cut(byValue, bounds.min(), own == null ? null : own.min(), "min",
                bounds.carrier(), under);
        cut(byValue, bounds.max(), own == null ? null : own.max(), "max",
                bounds.carrier(), over);
        return List.copyOf(byValue.values());
    }

    /** One end as a cut, owed once to each rule that put it there. */
    private static void cut(Map<String, Cut> into, DeclaredBounds.End end, DeclaredBounds.End own,
                            String clause, Carrier carrier, List<TypeSymbol> within) {
        if (end == null) {
            return;
        }
        // Taken in, which a record can do by moving the end or by taking away the value it stops
        // at. `low < high` under one `[0, 1]` leaves `low` the same 1 and no longer holding it, and
        // that is the record's doing as much as a smaller number would have been.
        boolean moved = own != null && !own.at().equals(end.at());
        for (TypeSymbol from : end.from()) {
            put(into, carrier, end.value(), from, clause, moved ? within : List.<TypeSymbol>of());
        }
    }

    private static void put(Map<String, Cut> into, Carrier carrier, Place at, TypeSymbol type,
                            String clause, List<TypeSymbol> narrowedBy) {
        OriginRef origin = new OriginRef.InvariantOrigin(type, clause);
        if (!narrowedBy.isEmpty()) {
            origin = new OriginRef.NarrowedOrigin(origin, narrowedBy);
        }
        OriginRef each = origin;
        Cut cut = Cut.at(carrier, at, origin);
        into.merge(cut.key(), cut, (had, _) -> had.and(each));
    }
}
