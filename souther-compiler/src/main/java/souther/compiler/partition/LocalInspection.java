package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Carrier;
import souther.compiler.check.InvariantBound;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.codegen.InvariantConstraints;
import souther.compiler.diag.SourceRef;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * What a position's own type and rules say about it, asked once and answered whole.
 *
 * <p>Two producers answer here — the classes the type states, and the lines its rules draw — and a
 * caller cannot ask one without the other. That is the point of the type: {@link Exhausted} is not
 * "there were no classes", it is <b>both were asked and neither had anything</b>, and only that
 * licenses going on to ask what is under the position. Asked separately, the walk decided when
 * local evidence had run out by looking at two empty lists, and any reader that forgot one of them
 * would have concluded it from half the evidence.
 *
 * <p>The reading and the answer are apart. {@link LocalReading} is what the position was seen to
 * be — its term, what its rules leave it, what could not be read — and is the same value in either
 * case, because one reading produced both.
 */
public sealed interface LocalInspection {

    /** What the position was read as, which is the same whether anything came of it. */
    LocalReading reading();

    /**
     * Something the position's own type or rules said: classes, lines, or both.
     *
     * <p>Never neither. A value of this carrying no classes and no cuts would be an exhaustion
     * dressed as evidence, and the phase after this one would never be reached for it.
     */
    record Evidence(LocalReading reading, List<PartitionClass> classes, CutEvidence cuts)
            implements LocalInspection {

        public Evidence {
            classes = List.copyOf(classes);
            if (classes.isEmpty() && cuts instanceof CutEvidence.None) {
                throw new IllegalArgumentException(
                        "neither classes nor cuts is `Exhausted`, which is a different answer");
            }
        }
    }

    /**
     * Both producers were asked and neither answered.
     *
     * <p>A proof rather than a report: what makes it constructible is having asked, and what it
     * licenses is the structural question after it. It says nothing about whether the position
     * divides — the rules a body writes have not been read yet.
     */
    record Exhausted(LocalReading reading) implements LocalInspection {}

    /**
     * The one reading.
     *
     * @param view   the position's type, read once
     * @param path   where the position sits, which a term is named by
     * @param placed the value the position is inside, or null where it is a parameter itself
     */
    static LocalInspection inspect(TypeView view, TermPath path, Symbols symbols,
                                   Partitions.Placed placed) {
        Type type = view.declared();
        // Which number this position is measured at, and what its rules leave that number. Asked
        // together because they are one reading: whether a rule bounds the length of a string is how
        // it is known that the length is the number being measured.
        Carrier carried = Carrier.ofValue(type, symbols);
        ValueName.Stdlib taken = NumericMeasures.takenOf(type, symbols);
        // What the rules are about, and only then what the type could carry. A position has one
        // axis, and a `String` is the one type that can be measured two ways — its own order, and
        // the length of it — so which of them the model wrote about is what decides. Read off the
        // carrier first, every rule anybody ever wrote about the length of a string would have
        // become a rule about the string.
        TypeBounds.Bounds sized = taken == null ? null
                : TypeBounds.of(type, symbols, Carrier.WHOLE, taken);
        boolean bySize = sized != null && !sized.isEmpty();
        NumericTerm term = bySize ? new NumericTerm.SizeOf(taken, path) : new NumericTerm.ValueOf(path);
        TypeBounds.Bounds own = bySize ? sized
                : carried == null ? null : TypeBounds.of(type, symbols, carried, null);
        // A value whose rules contradict has no positions to cover: every edge of every field of it
        // is a row nobody can write, which is not the same answer as a field nothing bounds.
        boolean nothingExists = placed != null && placed.domains().infeasible();
        // A record's rule relates the numbers its fields hold, so it reaches the term that is one of
        // them and no other: a cap on a field says nothing about how long the string beside it is.
        NumericDomain.Bounds projected = placed == null || !(term instanceof NumericTerm.ValueOf)
                ? null : placed.at(path);
        // Two questions of one pair of readings, and they do not have one answer. What the term's
        // values can be is every rule about it intersected; where it is divided is only where its own
        // type draws a line, because a clause relating two fields is not a partition of one of them.
        NumericDomain.Bounds admissible = nothingExists ? null
                : TypeBounds.admissible(own, projected, term);
        LocalReading reading = new LocalReading(term, admissible,
                unreadBoundsAt(path, type, symbols, carried, taken));

        // What the type declares, crossed with what the position can hold. Neither reading is the
        // other's input: a case the rules refuse is still a case of the type, and it is here that
        // it stops being a class of this position.
        List<PartitionClass> classes =
                constructibleAt(PartitionClasses.of(view, symbols), view, admissible, symbols);
        TypeBounds.Bounds axis = nothingExists ? null : axisBounds(own, projected);
        List<Cut> cuts = nothingExists ? List.of()
                : cutsOf(type, axis, own, placed == null ? null : placed.value());
        if (classes.isEmpty() && cuts.isEmpty()) {
            return new Exhausted(reading);
        }
        // Whether a row can be written at an edge is a question about the whole value the position
        // sits in, so it is answered once for the parameter. A rule this could not read is a way that
        // value can be refused, wherever in it the rule is written.
        CutEvidence drawn = cuts.isEmpty() ? new CutEvidence.None()
                : new CutEvidence.Present(cuts,
                        placed != null && !placed.domains().allRulesRead());
        return new Evidence(reading, classes, drawn);
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
     * @param within what the rules on the position leave its values, or null where nothing bounds
     *               them
     */
    private static List<PartitionClass> constructibleAt(List<PartitionClass> declared, TypeView view,
                                                        NumericDomain.Bounds within,
                                                        Symbols symbols) {
        if (within == null || declared.isEmpty()
                || !(Carrier.ofValue(view.declared(), symbols) instanceof Carrier.Ordinal order)) {
            return declared;   // no order for a rule to name a value on, so nothing is taken away
        }
        Set<String> refused = new LinkedHashSet<>();
        for (TypeName each : order.cases()) {
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
            for (Ast.InvariantClause clause : TypeOps.effectiveInvariants(layer.data(), symbols)) {
                for (Ast.Expr each : InvariantConstraints.clauses(clause.expr())) {
                    UndividedPosition.Reason why = whyUnread(each, carried, measure);
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
    private static UndividedPosition.Reason whyUnread(Ast.Expr clause, Carrier carried,
                                                      ValueName measure) {
        if (InvariantBound.statesAnEnd(clause, null)) {
            if (carried == null) {
                // The value is ordered — it is compared in the clause — and this reads no line on
                // what carries it. The carrier, asked of the carrier, as a guard's is.
                return UndividedPosition.Reason.UNSUPPORTED_DOMAIN;
            }
            return InvariantBound.of(clause, carried).isPresent()
                    ? null : UndividedPosition.Reason.UNSUPPORTED_SYNTAX;
        }
        if (measure != null && InvariantBound.statesAnEnd(clause, measure)) {
            // A size is a whole number whatever it is a size of, so nothing here is about a carrier.
            return InvariantBound.ofSize(clause, measure).isPresent() ? null
                    : UndividedPosition.Reason.UNSUPPORTED_SYNTAX;
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
    private static TypeBounds.Bounds axisBounds(TypeBounds.Bounds own,
                                                NumericDomain.Bounds projected) {
        if (own == null || projected == null) {
            return own;
        }
        // The value moves and the names do not: a record narrowing an edge does not take it away
        // from the rule that put one there, and which record did the narrowing is said beside it.
        return new TypeBounds.Bounds(
                own.min() == null ? null
                        : new TypeBounds.End(Endpoint.lower(own.min().at(), projected.min()),
                                own.min().from()),
                own.max() == null ? null
                        : new TypeBounds.End(Endpoint.upper(own.max().at(), projected.max()),
                                own.max().from()),
                own.carrier());
    }

    /**
     * The cuts of a position whose range is already settled.
     *
     * @param bounds where the position stops, the record it sits in taken into account
     * @param own    where its own type stops, so that an end the record moved can say so
     * @param within the record, or null at a position that is not a field of one
     */
    private static List<Cut> cutsOf(Type type, TypeBounds.Bounds bounds, TypeBounds.Bounds own,
                                    TypeName within) {
        if (bounds == null || bounds.isEmpty() || !(type instanceof Type.Ref)) {
            return List.of();
        }
        Map<String, Cut> byValue = new LinkedHashMap<>();
        cut(byValue, bounds.min(), own == null ? null : own.min(), "min",
                bounds.carrier(), within);
        cut(byValue, bounds.max(), own == null ? null : own.max(), "max",
                bounds.carrier(), within);
        return List.copyOf(byValue.values());
    }

    /** One end as a cut, owed once to each rule that put it there. */
    private static void cut(Map<String, Cut> into, TypeBounds.End end, TypeBounds.End own,
                            String clause, Carrier carrier, TypeName within) {
        if (end == null) {
            return;
        }
        // Taken in, which a record can do by moving the end or by taking away the value it stops
        // at. `low < high` under one `[0, 1]` leaves `low` the same 1 and no longer holding it, and
        // that is the record's doing as much as a smaller number would have been.
        boolean moved = own != null && !own.at().equals(end.at());
        for (TypeName from : end.from()) {
            put(into, carrier, end.value(), from, clause, moved ? within : null);
        }
    }

    private static void put(Map<String, Cut> into, Carrier carrier, Place at, TypeName type,
                            String clause, TypeName narrowedBy) {
        OriginRef origin = new OriginRef.InvariantOrigin(Optional.<SourceRef>empty(), type, clause);
        if (narrowedBy != null) {
            origin = new OriginRef.NarrowedOrigin(origin, narrowedBy);
        }
        OriginRef each = origin;
        Cut cut = Cut.at(carrier, at, origin);
        into.merge(cut.key(), cut, (had, _) -> had.and(each));
    }
}
