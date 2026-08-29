package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
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
     * <p>Keyed by the term and not by the path it is under. A count taken of a location and the
     * location's own content sit at one path and are not one thing to write: four is not what goes
     * at a position bounded on its length, it is four characters somebody has to choose.
     *
     * <p>And keyed by a number one position answers, because that is what a search can settle. What
     * this holds is an assignment — somewhere a row is asked to hold a value — so a number read
     * from anywhere but a single place has nothing to be assigned here, whatever else may be true
     * of it. Such a number can stand in a form a border is drawn on and be read off a row; what it
     * cannot be is an entry in this map, and the type is where that is said rather than at whichever
     * reader noticed.
     */
    record Found(Map<NumericTerm.FromOnePosition, Place> fixing) implements Realization {

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
