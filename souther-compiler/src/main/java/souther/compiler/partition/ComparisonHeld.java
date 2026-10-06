package souther.compiler.partition;

import souther.compiler.coverage.ControlPlace;
import souther.compiler.numeric.Place;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

/**
 * What a row has to be for one comparison of the body to come out one way where the body reaches
 * it.
 *
 * <p>Demands and not assignments, in the vocabulary a point of a border is composed in: where each
 * term the comparison reads has to stand ({@link Realization.Found#fixing}), every number it may
 * take there, and the way the comparison is reached by. So a term no position holds on its own —
 * the sum of what a list's elements hold — is a demand on whatever writes the list, and the
 * elements are composed to meet it.
 *
 * <p>Something a row is held to beside the classes it is composed for, and never one of them. What
 * the row is for is the classes; this is what it takes to get the row past a comparison that
 * stopped it.
 *
 * @param fixing   where the terms of the comparison stand, at a place on the side it comes out on
 * @param asking   every number each of those terms may take and still be on that side
 * @param reaching what the way to the comparison asks of the row
 */
public record ComparisonHeld(Map<RealizationTarget, Place> fixing, NumbersAskedFor asking,
                             Reachability.Reaching reaching) {

    public ComparisonHeld {
        // In the order the search fixed them, which a reader walking the demands meets them in.
        fixing = Collections.unmodifiableMap(new LinkedHashMap<>(fixing));
        if (fixing.isEmpty()) {
            throw new IllegalArgumentException("a comparison held is a term standing somewhere");
        }
    }

    /**
     * What holds each comparison of one behavior, asked for one comparison at a time.
     *
     * <p>Asked rather than handed over whole. Working one out is a search for a place, and the
     * comparisons a generation asks about are the few a row stopped at.
     *
     * <p>By where a run through the comparison is recorded and which way it is to come out, because
     * that is what a run is checked against: what got a row past a guard is the comparison coming
     * out the way the guard's condition needs, which is false as often as true — under
     * {@code Bool.not(x <= 0)} it is {@code x <= 0} failing.
     */
    @FunctionalInterface
    public interface Of {

        /** What brings the comparison out the way {@code outcome} says, or empty where nothing was
         *  found that does. */
        Optional<ComparisonHeld> at(ControlPlace.Outcome outcome);

        /** Nothing holds any comparison — what a caller with no borders to read uses. */
        Of NOTHING = _ -> Optional.empty();
    }
}
