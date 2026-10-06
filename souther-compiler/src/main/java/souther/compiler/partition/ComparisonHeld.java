package souther.compiler.partition;

import souther.compiler.coverage.ComparisonEmissionSite;
import souther.compiler.numeric.Place;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What a row has to be for one comparison of the body to hold where the body reaches it.
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
 * @param fixing   where the terms of the comparison stand, at a place on the side it holds on
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
     * <p>By where a run through the comparison is recorded, because what says a row stopped at one
     * is the run: it came out of the comparison the way that did not let it go on. Read off a
     * reading of the way in, a comparison of a number no reading can enumerate a way to — the total
     * of a list — would be one nothing could name.
     */
    public interface Of {

        /** Where each comparison this can say something about is recorded, in a steady order. */
        List<ComparisonEmissionSite> sites();

        /** What holds the comparison recorded at {@code site}, or empty where nothing was found
         *  that does. */
        Optional<ComparisonHeld> at(ComparisonEmissionSite site);

        /** Nothing holds any comparison — what a caller with no borders to read uses. */
        Of NOTHING = new Of() {

            @Override
            public List<ComparisonEmissionSite> sites() {
                return List.of();
            }

            @Override
            public Optional<ComparisonHeld> at(ComparisonEmissionSite site) {
                return Optional.empty();
            }
        };
    }
}
