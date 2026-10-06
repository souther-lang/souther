package souther.compiler.partition;

import souther.compiler.coverage.ControlPlace;

import java.util.Optional;

/**
 * What a row has to be for one condition of the body to come out one way where the body reaches
 * it.
 *
 * <p>Something a row is held to beside the classes it is composed for, and never one of them. What
 * the row is for is the classes; this is what it takes to get the row past a condition that
 * stopped it.
 *
 * <p>A demand and the way to the condition, and nothing about what the condition is. How the
 * demand was arrived at — a point of a comparison's border found by searching, or what an
 * operation's answer asks of the value it was asked of — is the producer's, so what composes a row
 * against these composes it against {@link RowDemand}s whichever condition stopped the row.
 *
 * @param demand   what the row has to be for the condition to come out that way
 * @param reaching what the way to the condition asks of the row — and, where the demand is one a
 *                 condition makes ({@link RowDemand.OfACondition}), the condition itself, which a
 *                 composer meets the way it meets every condition on the way
 */
public record HeldOutcome(RowDemand demand, Reachability.Reaching reaching) {

    /**
     * What holds each condition of one behavior, asked for one condition at a time.
     *
     * <p>Asked rather than handed over whole. Working one out can be a search for a place, and the
     * conditions a generation asks about are the few a row stopped at.
     *
     * <p>By where a run through the condition is recorded and which way it is to come out, because
     * that is what a run is checked against: what got a row past a guard is the condition coming
     * out the way the guard needs, which is false as often as true — under
     * {@code Bool.not(x <= 0)} it is {@code x <= 0} failing.
     */
    @FunctionalInterface
    public interface Of {

        /** What brings the condition out the way {@code outcome} says, or empty where nothing was
         *  found that does. */
        Optional<HeldOutcome> at(ControlPlace.Outcome outcome);

        /** Nothing holds any condition — what a caller with no borders to read uses. */
        Of NOTHING = _ -> Optional.empty();
    }
}
