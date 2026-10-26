package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
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

    /**
     * Two values of one case of a sum are a pair like any other, where the statement reads what
     * the case holds: they are taken after the pairs of different cases, and none is left out.
     */
    @Test
    void thePairsOfOneCaseAreTakenAfterThoseOfDifferentCasesAndNoneIsLeftOut() {
        List<ObservedValue> values = List.of(card(4), cash(4), card(6), cash(6), card(5));
        for (int value = 0; value < values.size() - 1; value++) {
            Set<KeyOrderCandidates.Pair> different = new HashSet<>(
                    KeyOrderCandidates.pairsWith(values, value, false));
            Set<KeyOrderCandidates.Pair> ofOneCase = new HashSet<>(
                    KeyOrderCandidates.pairsWith(values, value, true));
            Set<KeyOrderCandidates.Pair> every = new HashSet<>(
                    KeyOrderCandidates.pairsWith(values.size(), value));

            Set<KeyOrderCandidates.Pair> both = new HashSet<>(different);
            both.addAll(ofOneCase);
            assertEquals(every, both, "every pair of the round is in one of the two");
            assertTrue(different.stream().noneMatch(ofOneCase::contains),
                    "and in only one of them");
        }
        assertTrue(KeyOrderCandidates.pairsWith(values, 0, true)
                        .contains(new KeyOrderCandidates.Pair(0, 2)),
                "the two cards are a pair");
        assertTrue(KeyOrderCandidates.pairsWith(values, 0, false)
                        .contains(new KeyOrderCandidates.Pair(0, 1)),
                "a card and a cash are another");
    }

    /**
     * A value is refused on its own only where its type refuses it, and not where the whole it is
     * put in does: the one is a reason to leave it out of every pair, the other is not.
     */
    @Test
    void aValueIsRefusedOnItsOwnOnlyWhereItsTypeRefusesIt() {
        FixtureTemplate value = FixtureTemplate.string("x");
        Type type = Type.ref(TypeSymbols.declared(new TypeKey("g", "Pay")));
        Generator.CandidateCheck refusedBesideTheOthers = new Generator.CandidateCheck() {
            @Override
            public Generator.CandidateCheck.Built build(int parameter, FixtureTemplate candidate) {
                return new Generator.CandidateCheck.Built.Refused("the elements do not add up");
            }

            @Override
            public Admissibility admissibility(Type of, FixtureTemplate candidate) {
                return Admissibility.ADMITTED;
            }
        };
        Generator.CandidateCheck refusedOnItsOwn = new Generator.CandidateCheck() {
            @Override
            public Generator.CandidateCheck.Built build(int parameter, FixtureTemplate candidate) {
                return new Generator.CandidateCheck.Built.Refused("the type refuses it");
            }

            @Override
            public Admissibility admissibility(Type of, FixtureTemplate candidate) {
                return Admissibility.REFUSED;
            }
        };

        assertEquals(false, KeyOrderCandidates.refusedOnItsOwn(refusedBesideTheOthers, type, value));
        assertEquals(false, KeyOrderCandidates.refusedOnItsOwn(Generator.CandidateCheck.ANY, type,
                value), "nothing asked is nothing refused");
        assertEquals(true, KeyOrderCandidates.refusedOnItsOwn(refusedOnItsOwn, type, value));
    }

    private static ObservedValue card(long n) {
        return new ObservedValue.Constructed(TypeSymbols.declared(new TypeKey("g", "Card")),
                Map.of("n", new ObservedValue.Integer(n)));
    }

    private static ObservedValue cash(long n) {
        return new ObservedValue.Constructed(TypeSymbols.declared(new TypeKey("g", "Cash")),
                Map.of("n", new ObservedValue.Integer(n)));
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
