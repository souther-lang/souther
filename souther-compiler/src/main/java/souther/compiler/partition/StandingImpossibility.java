package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;

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
 * <p>A shape of {@link Standing} says which quantity is its own and how that quantity's values are
 * written, and nothing else is taken from it. The three differ in where the quantity is written — a
 * coordinate, the distance between two positions, a form over several — and in nothing that follows,
 * so what is asked of it is written once.
 */
final class StandingImpossibility {

    private StandingImpossibility() {}

    /**
     * Whether the region leaves {@code standing}'s quantity no value the item asks for.
     *
     * <p>Named for what a {@code true} is. What this decides is that a proof exists, and a name
     * saying whether the item can be satisfied would have {@code false} answering a question this
     * never asks.
     *
     * <p>{@code false} where the two meet and {@code false} where this could not put them in one
     * vocabulary, which is the same answer because the same thing follows from it. An absence of
     * proof reported as one takes a coverage item away, so everything this cannot tell apart is on
     * the side that proves nothing.
     */
    static boolean provesImpossible(SearchRegion region, Standing standing) {
        Asked asked = askedBy(standing);
        if (asked == null) {
            return false;
        }
        NumericDomain.Bounds runs = switch (region.projectionOf(asked.quantity())) {
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            // A form weighing no term is the one thing this answers nothing about, and an item
            // stands on a quantity — which is what the shapes of a Standing are built refusing.
            case null -> throw new IllegalStateException(
                    "an item stands on a quantity, and a form weighing no term is not one: "
                            + standing);
        };
        if (runs == null) {
            return true;
        }
        // Every run the item stands for, crossed with where the quantity runs. The crossing is the
        // interval algebra's own and not arithmetic written here: a run whose ends cross holds
        // nothing on any order, which is the one thing about a pair of runs that is true whatever
        // the order does between them — and it is the only half of the question that is sound in
        // one direction, since ends that do not cross say nothing about a value between them.
        LevelInterval possible = asked.runBetween(runs);
        for (LevelInterval part : asked.where().region().parts()) {
            if (part.intersect(possible) != null) {
                return false;
            }
        }
        return true;
    }

    /**
     * What an item asks, as this question needs it: the quantity, the values of it the item stands
     * for, and how those values are written.
     *
     * @param on the carrier the levels are values of, or null where the quantity counts its own
     *           numbers. Which is what tells a level of a coordinate from a level of a distance,
     *           and a run built with the wrong one would compare a place against a number
     */
    private record Asked(LinearForm<NumericTerm> quantity, Criterion where, Carrier on) {

        /** Where the quantity runs, in the words its own levels are written in. */
        LevelInterval runBetween(NumericDomain.Bounds runs) {
            return new LevelInterval(endAt(runs.min()), endAt(runs.max()));
        }

        /** One end of that run, as a level of the quantity. */
        private Bound endAt(Endpoint end) {
            if (end == null) {
                return null;
            }
            // A number where the quantity counts and a place of the carrier where it does not, and
            // which of the two it is was settled before anything was projected. A quantity that
            // counts is the sum or difference of positions that count, and a position whose values
            // do not count is only ever spoken of on its own order — so an end that is no number
            // arrives only at the shape holding the carrier to write it on.
            Level level = on == null ? new Level.ACount(Count.number(end.at()))
                    : new Level.OnACarrier(on, end.at());
            return Bound.at(level, end.inclusive());
        }
    }

    /**
     * The item taken apart that far, or nothing where its levels and the region's answer are not in
     * one vocabulary.
     *
     * <p>Which is a pair on an order that counts nothing, and only that. Two strings stand no
     * measurable distance apart, so the one level such a quantity takes is the one where they meet
     * and what a point of it asks is which way round they stand — while what the region has to say
     * about the pair is arithmetic over positions that add. Crossed as though they were one order,
     * a sign would have been compared against a bound and whichever answer came back would have
     * been read as a proof.
     */
    private static Asked askedBy(Standing standing) {
        return switch (standing) {
            case Standing.OfOneCoordinate one ->
                    new Asked(LinearForm.atom(one.term()), one.where(), one.of());
            case Standing.OfTwoOnOneCarrier two -> two.of().counts()
                    ? new Asked(LinearForm.<NumericTerm>atom(two.on())
                            .minus(LinearForm.atom(two.against())), two.where(), null)
                    : null;
            // A form is arithmetic over positions that add up, so its levels are numbers of its own
            // and the carriers its terms are written back on are no part of what it comes to.
            case Standing.OfAForm over -> new Asked(over.form(), over.where(), null);
        };
    }
}
