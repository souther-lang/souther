package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.Clause;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.RuleRef;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.Position;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What a position's own declarations divide it into, derived from the one reading of it.
 *
 * <p>The derivation is one way: a {@link Position} is read, and the answer follows from it. That is
 * what {@link LocalPartition.Open} means and how it is held — {@code Open} has nothing of its own
 * with which to contradict a reading, and there is no way to pair one with a reading that did not
 * run to the end, because there is no way to write a reading down here at all.
 *
 * <p>Which distinctions the position has is not decided here. It is asked of the position, which is
 * what keeps this from being a second crossing of the rules: what is added here is how a value of
 * one is named, recognised in a row, and written down.
 */
final class LocalInspection {

    /**
     * What {@code position} comes to.
     *
     * <p>A position whose rules leave it nothing is asked for its distinctions like any other: the
     * widening that hands the declared ones back belongs to the position, so a reader applying one
     * of its own here would be making that decision a second time and in another place.
     */
    static LocalPartition of(Position position, Symbols symbols) {
        List<PartitionClass> classes =
                PartitionClasses.of(position.obligationCases(), position.view(), symbols);
        DeclaredBounds.Bounds axis = position.nothingExists() ? null
                : axisBounds(position.ownEnds(), position.rangeLeft());
        List<Cut> cuts = position.nothingExists() ? List.of()
                : cutsOf(axis, position.ownEnds(),
                        position.narrowedBy(true), position.narrowedBy(false));
        if (classes.isEmpty() && cuts.isEmpty()) {
            // Nothing divides the position, and what may be concluded from that is what the reading
            // knows about itself. A set of values arrived at from part of the rules names no
            // division; a rule that went unread can divide the position as easily as one that was
            // read, so an absence does not follow from this reading having found none.
            return position.valuesUnread() == null ? new LocalPartition.Open()
                    : new LocalPartition.Blocked(position.valuesUnread());
        }
        // Whether a row can be written at an edge is a question about the whole value the position
        // sits in, so it is answered once for the parameter. A rule this could not read is a way
        // that value can be refused, wherever in it the rule is written.
        CutEvidence drawn = cuts.isEmpty() ? new CutEvidence.None()
                : new CutEvidence.Present(cuts, position.projection());
        return new LocalPartition.Divided(classes, drawn, position.unansweredQuestions(),
                position.rulesNotReached());
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
     * the record alone became invisible: see {@code TypeBounds#admissible}.
     */
    private static DeclaredBounds.Bounds axisBounds(DeclaredBounds.Bounds own,
                                                    NumericDomain.Bounds left) {
        if (own == null || left == null) {
            return own;
        }
        // The value moves and the names do not: a record narrowing an edge does not take it away
        // from the rule that put one there, and which record did the narrowing is said beside it.
        return new DeclaredBounds.Bounds(
                own.min() == null ? null
                        : new DeclaredBounds.End(Endpoint.lower(own.min().at(), left.min()),
                                own.min().from()),
                own.max() == null ? null
                        : new DeclaredBounds.End(Endpoint.upper(own.max().at(), left.max()),
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
    private static List<Cut> cutsOf(DeclaredBounds.Bounds bounds, DeclaredBounds.Bounds own,
                                    List<TypeSymbol> under, List<TypeSymbol> over) {
        // Nothing about the shape of the position's type. An end is here because some clause placed
        // it, and a clause naming a field of a record places one on a bare `Int` and on the length
        // of a bare `List<Int>` as readily as on a newtype over either.
        if (bounds == null || bounds.isEmpty()) {
            return List.of();
        }
        Map<String, Cut> byValue = new LinkedHashMap<>();
        cut(byValue, bounds.min(), own == null ? null : own.min(), bounds.carrier(), under);
        cut(byValue, bounds.max(), own == null ? null : own.max(), bounds.carrier(), over);
        return List.copyOf(byValue.values());
    }

    /** One end as a cut, owed once to each rule that put it there. */
    private static void cut(Map<String, Cut> into, DeclaredBounds.End end, DeclaredBounds.End own,
                            Carrier carrier, List<TypeSymbol> within) {
        if (end == null) {
            return;
        }
        // Taken in, which a record can do by moving the end or by taking away the value it stops
        // at. `low < high` under one `[0, 1]` leaves `low` the same 1 and no longer holding it, and
        // that is the record's doing as much as a smaller number would have been.
        boolean moved = own != null && !own.at().equals(end.at());
        // Wrapped here, and this is not a consumer settling what a rule is: which rule drew the end
        // was settled where the clause was read and arrives as it was. What is added is a
        // boundary's own answer about that rule — that a reading of it drew this cut, taken in by
        // these declarations — which is nothing the rule says about itself.
        for (RuleRef.Invariant from : end.from()) {
            put(into, carrier, end.value(), new OriginRef.InvariantOrigin(from, end.at().inclusive()),
                    moved ? within : List.<TypeSymbol>of());
        }
    }

    private static void put(Map<String, Cut> into, Carrier carrier, Place at, OriginRef drawnBy,
                            List<TypeSymbol> narrowedBy) {
        // The rule as the end already names it. Narrowing is the one thing said here, and it is
        // said about the rule rather than in place of it: which declarations took the end in is a
        // fact about this reading of the position, and what drew the end is not.
        OriginRef origin = narrowedBy.isEmpty() ? drawnBy
                : new OriginRef.NarrowedOrigin(drawnBy, narrowedBy);
        Cut cut = Cut.at(carrier, at, origin);
        into.merge(cut.key(), cut, (had, _) -> had.and(origin));
    }

    private LocalInspection() {}
}
