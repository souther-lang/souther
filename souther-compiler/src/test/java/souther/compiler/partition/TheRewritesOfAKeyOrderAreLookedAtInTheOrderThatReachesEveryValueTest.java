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

    /** The sites by rank are an element held again and a pair of elements in turn, as two plain
     *  lists merged by hand. */
    @Test
    void theSitesAreAnElementHeldAgainAndAPairOfElementsInTurn() {
        for (int size = 0; size <= 12; size++) {
            List<KeyOrderCandidates.Site> repeats = new ArrayList<>();
            for (int at = 0; at < size; at++) {
                repeats.add(new KeyOrderCandidates.Site.Repeating(at));
            }
            List<KeyOrderCandidates.Site> pairs = new ArrayList<>();
            for (int first = 0; first < size; first++) {
                for (int second = first + 1; second < size; second++) {
                    pairs.add(new KeyOrderCandidates.Site.Overwriting(first, second));
                }
            }
            List<KeyOrderCandidates.Site> listed = new ArrayList<>();
            for (int at = 0; at < Math.max(repeats.size(), pairs.size()); at++) {
                if (at < repeats.size()) {
                    listed.add(repeats.get(at));
                }
                if (at < pairs.size()) {
                    listed.add(pairs.get(at));
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

    /**
     * A round is visited whether or not it yields a rewrite, so the bound on what is looked at
     * does not bound them: the rounds are bounded by the values and the sites, however many
     * elements a container holds.
     */
    @Test
    void theRoundsAreBoundedByTheValuesAndTheSitesWhateverTheContainerHolds() {
        long most = (long) (MOST_VALUES - 1) * KeyOrderCandidates.MOST_SITES_OF_A_CONTAINER;

        assertEquals((long) (MOST_VALUES - 1) * 3,
                KeyOrderCandidates.roundsOf(MOST_VALUES, 3).count(),
                "a container with fewer sites than the most has the rounds of its own");
        assertEquals(most, KeyOrderCandidates.roundsOf(MOST_VALUES,
                KeyOrderCandidates.sitesIn(1000)).count());
        assertEquals(most, KeyOrderCandidates.roundsOf(MOST_VALUES, Integer.MAX_VALUE).count());
        assertEquals(new KeyOrderCandidates.Site.Repeating(15),
                KeyOrderCandidates.siteAt(1000, 30), "the sites visited of a long container");
        assertEquals(new KeyOrderCandidates.Site.Overwriting(0, 16),
                KeyOrderCandidates.siteAt(1000, 31));
    }

    /**
     * Within the rewrites that are looked at, a round holds both the pairs of different cases and
     * the pairs of one case, at the first site and at each site after it, so that neither kind
     * is put out of reach by the other using the bound up.
     */
    @Test
    void bothKindsOfPairAreAmongTheRewritesLookedAtAtEverySiteTheyReach() {
        List<ObservedValue> values = List.of(card(0), cash(0), card(1), cash(1), card(2),
                cash(2));
        int looked = 0;
        Set<Integer> sitesOfDifferentCases = new HashSet<>();
        Set<Integer> sitesOfOneCase = new HashSet<>();
        for (KeyOrderCandidates.Round round
                : KeyOrderCandidates.roundsOf(values.size(), KeyOrderCandidates.sitesIn(5))
                        .toList()) {
            for (KeyOrderCandidates.Pair pair
                    : KeyOrderCandidates.pairsOfRound(values, round.value())) {
                if (looked++ >= KeyOrderCandidates.MOST_REWRITES_LOOKED_AT) {
                    break;
                }
                boolean cards = (pair.earlier() % 2) == (pair.later() % 2);
                (cards ? sitesOfOneCase : sitesOfDifferentCases).add(round.site());
            }
        }
        assertTrue(sitesOfOneCase.contains(0) && sitesOfDifferentCases.contains(0),
                "both at the first site");
        assertEquals(sitesOfDifferentCases, sitesOfOneCase,
                "and at every site the bound reaches");
    }

    /**
     * A bound on the sites visited, or on the rewrites looked at, cuts the end of the order, and
     * what it must not cut is a kind of site: however long the container is and wherever the bound
     * falls after the first two sites, an element held again and a pair of elements are both in
     * what is visited. A container of fixed length is refused every element held again, and one
     * whose elements may not repeat a key is refused every pair, so each is the only way to a row
     * for some model.
     */
    @Test
    void anyPrefixOfTheSitesOfAContainerOfSeveralElementsHoldsBothKinds() {
        for (int size : new int[] {2, 3, 5, 12, 33, 1000}) {
            for (int visited = 2; visited <= Math.min(KeyOrderCandidates.MOST_SITES_OF_A_CONTAINER,
                    KeyOrderCandidates.sitesIn(size)); visited++) {
                boolean repeating = false;
                boolean overwriting = false;
                for (int rank = 0; rank < visited; rank++) {
                    switch (KeyOrderCandidates.siteAt(size, rank)) {
                        case KeyOrderCandidates.Site.Repeating _ -> repeating = true;
                        case KeyOrderCandidates.Site.Overwriting _ -> overwriting = true;
                    }
                }
                assertTrue(repeating && overwriting, size + " elements, " + visited + " sites");
            }
        }
    }

    /**
     * The same where the bound is the one on the rewrites looked at: a value is paired with the
     * others at each site in turn, and the sites it reaches before the bound is used up have both
     * kinds, though the pairs of one site are many.
     */
    @Test
    void theRewritesLookedAtReachBothKindsOfSiteWhateverTheValuesAreMany() {
        for (int elements : new int[] {2, 4, 33}) {
            int looked = 0;
            boolean repeating = false;
            boolean overwriting = false;
            for (KeyOrderCandidates.Round round
                    : KeyOrderCandidates.roundsOf(MOST_VALUES, KeyOrderCandidates.sitesIn(elements))
                            .toList()) {
                if (looked >= KeyOrderCandidates.MOST_REWRITES_LOOKED_AT) {
                    break;
                }
                looked += KeyOrderCandidates.pairsWith(MOST_VALUES, round.value()).size();
                switch (KeyOrderCandidates.siteAt(elements, round.site())) {
                    case KeyOrderCandidates.Site.Repeating _ -> repeating = true;
                    case KeyOrderCandidates.Site.Overwriting _ -> overwriting = true;
                }
            }
            assertTrue(repeating && overwriting, elements + " elements");
        }
    }

    /** The fields of a round take their pairs in turn, so a field with many does not use up what
     *  is looked at before a field with few has had its first. */
    @Test
    void theFieldsOfARoundTakeTheirPairsInTurn() {
        assertEquals(List.of(new KeyOrderCandidates.Turn(0, 0), new KeyOrderCandidates.Turn(1, 0),
                        new KeyOrderCandidates.Turn(2, 0), new KeyOrderCandidates.Turn(0, 1),
                        new KeyOrderCandidates.Turn(2, 1), new KeyOrderCandidates.Turn(0, 2)),
                KeyOrderCandidates.turnsOf(new int[] {3, 1, 2}));
        assertEquals(List.of(), KeyOrderCandidates.turnsOf(new int[] {}));
        assertEquals(List.of(), KeyOrderCandidates.turnsOf(new int[] {0, 0}));
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
