package souther.compiler.partition;

import souther.compiler.numeric.Place;

import java.util.Map;

/**
 * What looking for a row at one coverage item came to.
 *
 * <p><b>Three answers, because two of them mean opposite things.</b> That the rules leave no row
 * there and that this compiler's search did not find one are different facts: the first takes the
 * item away, and the second leaves it owed and unsettled (ADR-0091). Held as an empty {@code
 * Optional} they were one, and a search that ran out of budget read as a proof that the model
 * refuses the edge.
 */
public sealed interface Realization {

    /**
     * Where each of the item's terms has to stand for the row to be at it.
     *
     * <p><b>Demands and not assignments.</b> An entry says that this number is to answer this place,
     * and the key says which value a row rebuilds to make it do so — which for a number one position
     * answers is that position, and for a number taken over a run is the sequence its values are
     * read from. The place is what the term answers and never what is written at the root: no total
     * is written at a list.
     *
     * <p>Keyed by the target and not by the path it writes. A count taken of a location and the
     * location's own content are one path and two demands: four is not what goes at a position
     * bounded on its length, it is four characters somebody has to choose. Whether two demands can
     * be met by one row is {@link LocationWrites}' answer and is not readable off this map, which
     * holds them apart precisely so that nothing collapses them early.
     *
     * <p>And not keyed by the term, though every target has one. What a reader of this does is
     * write, and a term does not say where a row writes ({@link RealizationTarget}).
     */
    record Found(Map<RealizationTarget, Place> fixing) implements Realization {

        public Found {
            fixing = Map.copyOf(fixing);
        }
    }

    /**
     * The rules leave nothing at this item, and that is proved rather than searched for.
     *
     * <p>What a report counts as excluded and what a build is not refused over. Only a proof reaches
     * here: two ends that have crossed, an order with nothing past its last value.
     */
    record Impossible() implements Realization {}

    /**
     * Nothing came of the search, and nothing follows about whether a row exists.
     *
     * <p>The item stays owed. What a report says of it is that it is not known to be writable, which
     * is the account any unpromised edge gets.
     */
    record Unknown(Reason why, java.util.Set<CompositionBudget> stoppedBy)
            implements Realization {

        public Unknown {
            stoppedBy = java.util.Set.copyOf(stoppedBy);
            // What a walk stopped by these says is the budgets' to say, so the two cannot be put
            // here disagreeing. A pair that could is a pair somebody has to keep in step, and
            // keeping two spellings of one answer in step by hand is what a stopped walk lost its
            // budget to in the first place.
            if (!stoppedBy.isEmpty()
                    && why != Generator.UnresolvedCombination.Reason.wordFor(stoppedBy)
                            .asAWalksAnswer()) {
                throw new IllegalArgumentException("a walk stopped by " + stoppedBy
                        + " does not come back with " + why);
            }
        }

        /**
         * A walk that composed no candidate, and the budgets of this compiler's it ran out of.
         *
         * <p><b>The word is the walk's and the budgets are beside it.</b> What a walk came to and
         * whether a figure of this compiler's stopped it are two questions, and only the first has
         * ever decided which word this comes back with. Made from the budgets instead — one word
         * where some were reached and another where none were — a walk changes what it says by
         * acquiring a fact about this compiler, and a reader who has been reading that word for
         * reasons of their own is told something else.
         *
         * <p>Empty is the ordinary case and says the same thing: nothing was composed, and nothing
         * of this compiler's is why.
         */
        public static Unknown nothingComposedOne(java.util.Set<CompositionBudget> stoppedBy) {
            return new Unknown(Reason.NOTHING_COMPOSED_ONE, stoppedBy);
        }

        /** The same, of a walk that composed no candidate and met no figure. */
        public static Unknown nothingComposedOne() {
            return nothingComposedOne(java.util.Set.of());
        }

        /**
         * A walk that tried what it had and settled nothing, and the budgets it ran out of.
         *
         * <p>Beside {@link #nothingComposedOne} for the reason above: which of the two a walk says
         * is the walk's own answer, and this one is what a side comes back with whether or not a
         * figure was reached.
         */
        public static Unknown searchRanOut(java.util.Set<CompositionBudget> stoppedBy) {
            return new Unknown(Reason.THE_SEARCH_RAN_OUT, stoppedBy);
        }

        public enum Reason {
            /** This compiler composed no candidate — a position whose type it cannot write at, a
             *  term that is a measure of a value rather than the value. */
            NOTHING_COMPOSED_ONE,
            /** Candidates were tried and the search stopped before it settled the question. */
            THE_SEARCH_RAN_OUT
        }
    }
}
