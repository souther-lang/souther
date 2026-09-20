package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
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

        /**
         * Held in the terms' own order, so that a reader walking it meets the demands in the same
         * order in every run. Two demands of one term are told apart by where they write, compared
         * by every part of the path and not by how it is spelled.
         */
        public Found {
            Map<NumericTerm, List<RealizationTarget>> byTerm = new HashMap<>();
            for (RealizationTarget each : fixing.keySet()) {
                byTerm.computeIfAbsent(each.term(), _ -> new ArrayList<>()).add(each);
            }
            Map<RealizationTarget, Place> inOrder = new LinkedHashMap<>();
            for (NumericTerm term : NumericTerms.inOrder(byTerm.keySet())) {
                List<RealizationTarget> ofOne = byTerm.get(term);
                ofOne.sort(Comparator.comparing(RealizationTarget::writeRoot,
                        TermPath.structuralOrder()));
                for (RealizationTarget each : ofOne) {
                    inOrder.put(each, fixing.get(each));
                }
            }
            fixing = Collections.unmodifiableMap(inOrder);
        }
    }

    /**
     * The rules leave nothing at this item, and that is proved rather than searched for.
     *
     * <p>What a report counts as excluded and what a build is not refused over. Only a proof reaches
     * here: two ends that have crossed, an order with nothing past its last value, a region that
     * leaves the item's quantity no value the item asks for.
     */
    record Impossible() implements Realization {}

    /**
     * Nothing came of the search, and nothing follows about whether a row exists.
     *
     * <p>The item stays owed. What a report says of it is that it is not known to be writable, which
     * is the account any unpromised edge gets.
     *
     * <p><b>Two vocabularies for what was left untried, because what a reader does about them
     * differs.</b> {@code stoppedBy} is a figure somebody wrote down and raising it goes further;
     * {@code notAllOf} is a set this compiler has no way of producing the rest of, and raising
     * anything reaches none of it ({@link CompositionRepertoire}). Either may be empty and both may
     * be there. Held as one vocabulary, a reader is sent to raise a number that changes nothing —
     * and held as neither, a search that could name one place and no second one came back saying
     * what a search that had looked everywhere says.
     */
    record Unknown(Reason why, java.util.Set<CompositionBudget> stoppedBy,
                   java.util.Set<CompositionRepertoire> notAllOf)
            implements Realization {

        public Unknown {
            stoppedBy = java.util.Set.copyOf(stoppedBy);
            notAllOf = java.util.Set.copyOf(notAllOf);
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
            return new Unknown(Reason.NOTHING_COMPOSED_ONE, stoppedBy, java.util.Set.of());
        }

        /** The same, of a walk that composed no candidate and met no figure. */
        public static Unknown nothingComposedOne() {
            return nothingComposedOne(java.util.Set.of());
        }

        /**
         * A walk that tried what it had and settled nothing, and the budgets it met on the way.
         *
         * <p>Beside {@link #nothingComposedOne} for the reason above: which of the two a walk says
         * is the walk's own answer, and this one is what a side comes back with whether or not a
         * figure was reached. Which is why it is not named for running out — the figures are said
         * beside the answer and do not choose it.
         */
        public static Unknown searchLeftSomethingUntried(
                java.util.Set<CompositionBudget> stoppedBy) {
            return searchLeftSomethingUntried(stoppedBy, java.util.Set.of());
        }

        /**
         * The same, of a walk that also wrote some of a population rather than all of it.
         *
         * <p>Both, and neither stands for the other. A walk may meet a figure and separately be
         * unable to name the rest of what it was walking, and a reader owed only one of the two is
         * told either to raise something that was not what stopped it or that nothing of this
         * compiler's is why — of a walk that looked in one place.
         */
        public static Unknown searchLeftSomethingUntried(
                java.util.Set<CompositionBudget> stoppedBy,
                java.util.Set<CompositionRepertoire> notAllOf) {
            return new Unknown(Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED, stoppedBy, notAllOf);
        }

        public enum Reason {
            /** This compiler composed no candidate — a position whose type it cannot write at, a
             *  term that is a measure of a value rather than the value. */
            NOTHING_COMPOSED_ONE,
            /**
             * Candidates were tried and something was left untried before the question was
             * settled.
             *
             * <p>Not that the search stopped. A side is never settled by looking, so this is what
             * one comes back with whether or not a figure of this compiler's was reached — and a
             * word saying it halted would name a stop that may not have happened. What was left,
             * and whether raising anything reaches it, is said beside this.
             */
            THE_SEARCH_LEFT_SOMETHING_UNTRIED
        }
    }
}
