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
    record Unknown(Reason why) implements Realization {

        public enum Reason {
            /** This compiler composed no candidate — a position whose type it cannot write at, a
             *  term that is a measure of a value rather than the value. */
            NOTHING_COMPOSED_ONE,
            /** Candidates were tried and the search stopped before it settled the question. */
            THE_SEARCH_RAN_OUT
        }
    }
}
