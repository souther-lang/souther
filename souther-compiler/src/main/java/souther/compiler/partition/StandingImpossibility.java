package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;

/**
 * Whether the rules a row passes on the way to an item leave its quantity no value the item asks
 * for.
 *
 * <p><b>One direction only.</b> {@code true} is a proof that no row is at the item; {@code false} is
 * not the other proof and is not evidence of one. What it says is that this question did not settle
 * it — the two may meet at a place the order holds no value at, and whether one is there is the
 * search's answer. A caller that reads {@code false} as a row being writable has turned a sufficient
 * condition into an equivalence, which is the reading {@link Realization} keeps three answers for.
 *
 * <p>Which is why the crossing is the only thing here. Where the quantity runs is the region's
 * answer ({@link SearchRegion#projectionOf}) and which of its values stand at the item is the item's
 * ({@link Criterion#region()}); whether the two meet is a question neither of them answers, and
 * where nobody asks it a contradiction with a finite proof is handed to a search and comes back as
 * a figure of this compiler's. Nothing here reads a rule, walks an order or composes a value.
 *
 * <p>And why it is here rather than on the region. What a row has to satisfy is the item's
 * vocabulary and the region is the algebra underneath it; asked to answer about a {@link Standing},
 * the region would carry a second reading of what a criterion means, free to disagree with the one
 * the search uses.
 *
 * <p>A shape of {@link Standing} says which quantity is its own and nothing else is taken from it.
 * The three differ in where that quantity is written — a coordinate, the distance between two
 * positions, a form over several — and in nothing that follows, so what is asked of it is written
 * once.
 */
final class StandingImpossibility {

    private StandingImpossibility() {}

    /**
     * Whether the region leaves {@code standing}'s quantity no value the item asks for.
     *
     * <p>{@code false} wherever this could not answer, which is every shape of not knowing: a
     * quantity the arithmetic has no projection of, an end at a place that is not a number, an order
     * whose values the region speaks of in another vocabulary. An absence of proof reported as one
     * takes a coverage item away, so the cases that cannot be told apart are all on the side that
     * proves nothing.
     */
    static boolean cannotSatisfy(SearchRegion region, Standing standing) {
        Asked asked = askedBy(standing);
        NumericDomain.Bounds runs;
        switch (region.projectionOf(asked.quantity())) {
            case NumericDomain.FormProjection.NothingIsLeft _ -> {
                return true;
            }
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    runs = held == null ? NumericDomain.Bounds.OPEN : held;
            case null -> {
                return false;
            }
        }
        LevelInterval possible = runOf(runs, asked.on());
        if (possible == null) {
            return false;
        }
        // Every run the item stands for, crossed with where the quantity runs. The crossing is the
        // interval algebra's own and not arithmetic written here: a run whose ends cross holds
        // nothing on any order, which is the one thing about a pair of runs that is true whatever
        // the order does between them.
        for (LevelInterval part : asked.where().region().parts()) {
            if (part.intersect(possible) != null) {
                return false;
            }
        }
        return true;
    }

    /**
     * What an item asks, as this question needs it: the quantity, the values of it the item stands
     * for, and the order those values are written on.
     *
     * @param on the carrier the levels are values of, or null where they are numbers of no
     *           position's. Which is what tells a level of a coordinate from a level of a distance,
     *           and a run built with the wrong one would compare a place against a number
     */
    private record Asked(LinearForm<NumericTerm> quantity, Criterion where, Carrier on) {}

    /** The item taken apart that far, which is the whole of what a shape of {@link Standing} is
     *  read for here. */
    private static Asked askedBy(Standing standing) {
        return switch (standing) {
            case Standing.OfOneCoordinate one ->
                    new Asked(LinearForm.atom(one.term()), one.where(), one.of());
            case Standing.OfTwoOnOneCarrier two -> new Asked(
                    LinearForm.<NumericTerm>atom(two.on()).minus(LinearForm.atom(two.against())),
                    two.where(), null);
            case Standing.OfAForm over -> new Asked(over.form(), over.where(), null);
        };
    }

    /** Where the quantity runs, as a run of its own levels, or null where an end is at no level of
     *  it. */
    private static LevelInterval runOf(NumericDomain.Bounds runs, Carrier on) {
        Bound low = endOf(runs.min(), on);
        Bound high = endOf(runs.max(), on);
        if ((runs.min() != null && low == null) || (runs.max() != null && high == null)) {
            return null;
        }
        return new LevelInterval(low, high);
    }

    /** One end of that run, or null where the place it stops at is not a level of the quantity. */
    private static Bound endOf(Endpoint end, Carrier on) {
        if (end == null) {
            return null;
        }
        Place at = end.at();
        if (on != null) {
            return Bound.at(new Level.OnACarrier(on, at), end.inclusive());
        }
        return at instanceof Count count
                ? Bound.at(new Level.ACount(count), end.inclusive()) : null;
    }
}
