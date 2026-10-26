package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the rewrites for the order of a repeated key are written from is a product of the values
 * two copies are given, the sites they are written at and the containers and fields they are
 * written in, and a bound on how many are looked at cuts the end of the order they are taken in.
 * So the order is what says which values and which sites are reached, and it is held here as the
 * order alone, over the numbers the bounds are set against.
 *
 * <p>A value is taken against each of the others in both orders at one site before it is taken at
 * the next, so that a bound cuts later sites and later values and never a value for coming late
 * among many.
 */
class TheRewritesOfAKeyOrderAreLookedAtInTheOrderThatReachesEveryValueTest {

    /** The most values any field is given: every case of a sum, each with its values. */
    private static final int MOST_VALUES = KeyOrderCandidates.MOST_CASES_OF_A_SUM
            * KeyOrderCandidates.MOST_VALUES_OF_A_CASE;

    @Test
    void aValueIsTakenAgainstTheLaterOnesInBothOrdersAtOneSiteBeforeTheNextSite() {
        assertEquals(List.of(new KeyOrderCandidates.Round(0, 0), new KeyOrderCandidates.Round(0, 1),
                        new KeyOrderCandidates.Round(1, 0), new KeyOrderCandidates.Round(1, 1)),
                KeyOrderCandidates.roundsOf(3, 2).toList());
        assertEquals(List.of(new KeyOrderCandidates.Pair(1, 2), new KeyOrderCandidates.Pair(2, 1),
                        new KeyOrderCandidates.Pair(1, 3), new KeyOrderCandidates.Pair(3, 1)),
                KeyOrderCandidates.pairsWith(4, 1));
        assertEquals(List.of(), KeyOrderCandidates.roundsOf(1, 5).toList(),
                "one value has nothing to be taken against");
    }

    /** The sites by rank are the elements held again and then the pairs of elements, as listed
     *  by two plain loops. */
    @Test
    void theSitesAreTheElementsHeldAgainAndThenThePairsOfElements() {
        for (int size = 0; size <= 12; size++) {
            List<KeyOrderCandidates.Site> listed = new ArrayList<>();
            for (int at = 0; at < size; at++) {
                listed.add(new KeyOrderCandidates.Site.Repeating(at));
            }
            for (int first = 0; first < size; first++) {
                for (int second = first + 1; second < size; second++) {
                    listed.add(new KeyOrderCandidates.Site.Overwriting(first, second));
                }
            }
            List<KeyOrderCandidates.Site> byRank = new ArrayList<>();
            for (int rank = 0; rank < KeyOrderCandidates.sitesIn(size); rank++) {
                byRank.add(KeyOrderCandidates.siteAt(size, rank));
            }
            assertEquals(listed, byRank, "a container of " + size + " elements");
            assertEquals(null, KeyOrderCandidates.siteAt(size, listed.size()));
        }
        assertEquals(null, KeyOrderCandidates.siteAt(3, -1));
    }

    @Test
    void theNumberOfSitesOfALargeContainerDoesNotOverflow() {
        assertEquals(Integer.MAX_VALUE, KeyOrderCandidates.sitesIn(Integer.MAX_VALUE));
    }

    /**
     * However many elements the container holds, the rounds of the first value at the first site
     * reach every other value in both orders, and they are no more than are looked at: the pairs
     * of one site are {@code 2 × (values − 1)}, and it is the sites that grow with the elements.
     */
    @Test
    void theFirstSiteReachesEveryValueWithinTheBoundWhateverTheContainerHolds() {
        assertTrue(2 * (MOST_VALUES - 1) <= KeyOrderCandidates.MOST_REWRITES_LOOKED_AT,
                "the pairs of one value at one site are among the rewrites looked at");
        for (int elements : new int[] {1, 2, 4, 8, 16}) {
            int sites = KeyOrderCandidates.sitesIn(elements);
            List<KeyOrderCandidates.Pair> looked = new ArrayList<>();
            KeyOrderCandidates.roundsOf(MOST_VALUES, sites)
                    .takeWhile(round -> looked.size() < KeyOrderCandidates.MOST_REWRITES_LOOKED_AT)
                    .forEach(round -> {
                        if (round.site() == 0) {
                            looked.addAll(KeyOrderCandidates.pairsWith(MOST_VALUES,
                                    round.value()));
                        }
                    });
            Set<KeyOrderCandidates.Pair> first = new HashSet<>(
                    KeyOrderCandidates.pairsWith(MOST_VALUES, 0));
            assertTrue(looked.containsAll(first),
                    "with " + elements + " elements the first value meets every other");
            assertEquals(2 * (MOST_VALUES - 1), first.size());
        }
    }

    /**
     * Taken a site at a time, the rewrites looked at reach every value at the first site before
     * any value is written at a second, though the sites of a container are many.
     */
    @Test
    void aBoundCutsLaterSitesBeforeItCutsAValue() {
        int sites = KeyOrderCandidates.sitesIn(4);
        Set<Integer> valuesAtTheFirstSite = new HashSet<>();
        int looked = 0;
        for (KeyOrderCandidates.Round round
                : KeyOrderCandidates.roundsOf(MOST_VALUES, sites).toList()) {
            if (looked >= KeyOrderCandidates.MOST_REWRITES_LOOKED_AT) {
                break;
            }
            for (KeyOrderCandidates.Pair pair
                    : KeyOrderCandidates.pairsWith(MOST_VALUES, round.value())) {
                if (round.site() == 0) {
                    valuesAtTheFirstSite.add(pair.earlier());
                    valuesAtTheFirstSite.add(pair.later());
                }
                looked++;
            }
        }
        assertEquals(MOST_VALUES, valuesAtTheFirstSite.size(),
                "every value is written at the first site within the bound");
    }
}
