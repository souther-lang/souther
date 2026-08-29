package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which counts are worth telling apart, and what becomes of the rest.
 *
 * <p>The walk over the type graph rises until it stops changing, so it stops at all only because
 * there are finitely many answers to rise through. The numbers written in a model are not that: a set
 * asked to hold a million values would give a million of them to climb. What the transfers ever ask
 * of a count is whether it is too small to fill some collection, so only the answers those questions
 * turn on are kept, and everything else is rounded up to the next one that is.
 *
 * <p>Up and never down. A rounded count says the type may have more values than was shown, which
 * leaves a set that cannot be filled looking as though it might be — the direction that admits. That
 * a count of none is never rounded to anything is not asserted here: rounding takes and gives a
 * {@link Cardinality.Standing}, so there is no such call to make.
 */
class ARoundedCountKeepsTheComparisonsThatDecideTest {

    @Test
    void aCountIsKeptWhereACollectionAsksAboutIt() {
        // A set of two turns on whether its element has two, so one and none are told apart.
        CardinalityCuts cuts = CardinalityCuts.keeping(Set.of(2L));
        assertEquals(Cardinality.atMost(1), cuts.round(Cardinality.atMost(1)));
        assertEquals(1, cuts.round(Cardinality.atMost(1)).boundOr(-1), "still too small to fill it");
    }

    @Test
    void aCountAboveEveryQuestionIsNoLongerANumber() {
        CardinalityCuts cuts = CardinalityCuts.keeping(Set.of(2L));
        assertEquals(Cardinality.UNKNOWN, cuts.round(Cardinality.atMost(2)));
        assertEquals(Cardinality.UNKNOWN, cuts.round(Cardinality.atMost(1000)));
    }

    @Test
    void aCountBetweenTwoQuestionsRisesToTheHigherOne() {
        CardinalityCuts cuts = CardinalityCuts.keeping(List.of(2L, 1000L));
        assertEquals(Cardinality.atMost(999), cuts.round(Cardinality.atMost(700)));
        assertEquals(Cardinality.atMost(1), cuts.round(Cardinality.atMost(1)));
    }

    @Test
    void havingNoBoundIsNotRoundedAway() {
        assertEquals(Cardinality.UNKNOWN, CardinalityCuts.keeping(Set.of(2L)).round(Cardinality.UNKNOWN));
    }

    /** What the walk rises through, which is what makes it stop. */
    @Test
    void thereAreAsManyAnswersAsQuestionsAndTwoEnds() {
        assertEquals(3, CardinalityCuts.keeping(Set.of(2L)).answers());
        assertEquals(4, CardinalityCuts.keeping(List.of(2L, 1000L)).answers());
        assertEquals(2, CardinalityCuts.keeping(List.of()).answers());
    }

    /** A collection asking for none asks nothing: every count fills it. */
    @Test
    void aQuestionAboutNoneKeepsNoCount() {
        assertEquals(2, CardinalityCuts.keeping(List.of(0L)).answers());
    }

    @Test
    void roundingIsMonotone() {
        CardinalityCuts cuts = CardinalityCuts.keeping(List.of(2L, 1000L));
        List<Cardinality.Standing> rising = List.of(Cardinality.atMost(1), Cardinality.atMost(2),
                Cardinality.atMost(999), Cardinality.atMost(1000), Cardinality.UNKNOWN);
        for (int each = 1; each < rising.size(); each++) {
            assertTrue(cuts.round(rising.get(each)).boundOr(Long.MAX_VALUE)
                            >= cuts.round(rising.get(each - 1)).boundOr(Long.MAX_VALUE),
                    "rounding " + rising.get(each) + " after " + rising.get(each - 1));
        }
    }
}
