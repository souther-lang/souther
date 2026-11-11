package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A set held by its ends and remainders answers membership and the nearest members exactly, and
 * the meet of two is the numbers both hold, whichever way they are written.
 */
class WholeNumberSetTest {

    private static BigInteger n(long value) {
        return BigInteger.valueOf(value);
    }

    private static WholeNumberSet evens() {
        return WholeNumberSet.ofClass(new Congruences(BigInteger.ZERO, n(2)));
    }

    private static WholeNumberSet nonNegative() {
        return WholeNumberSet.ofRuns(WholeNumberRuns.one(BigInteger.ZERO, null));
    }

    @Test
    void theEvenNumbersAreHeldWithoutListingThem() {
        WholeNumberSet evens = evens();
        assertTrue(evens.holds(n(-4)));
        assertFalse(evens.holds(n(3)));
        assertEquals(n(2), evens.greatestAtOrBelow(n(3)));
        assertEquals(n(4), evens.leastAtOrAbove(n(3)));
        assertNull(evens.least());
    }

    @Test
    void theMeetOfEvensAndNonNegativesHasItsEndsAtMembers() {
        WholeNumberSet both = evens().and(nonNegative());
        assertEquals(n(0), both.least());
        assertNull(both.greatest());
        assertNull(both.greatestAtOrBelow(n(-1)));
        assertEquals(n(2), both.greatestAtOrBelow(n(3)));
    }

    /** Evens and odds share no number, and the multiples of two and of three share those of six. */
    @Test
    void twoRemaindersMeetWhereTheirCongruencesDo() {
        WholeNumberSet odds = WholeNumberSet.ofClass(new Congruences(BigInteger.ONE, n(2)));
        assertTrue(evens().and(odds).isNone());
        WholeNumberSet threes = WholeNumberSet.ofClass(new Congruences(BigInteger.ZERO, n(3)));
        WholeNumberSet sixes = evens().and(threes);
        assertTrue(sixes.holds(n(12)));
        assertFalse(sixes.holds(n(9)));
        assertFalse(sixes.holds(n(8)));
    }

    /** Nought and the numbers from six on, which a filter keeping six or more totals. */
    @Test
    void aSetOfRunsHoldsNoughtAndSixAndMoreAndNothingBetween() {
        WholeNumberSet kept = WholeNumberSet.ofRuns(WholeNumberRuns.one(BigInteger.ZERO,
                BigInteger.ZERO).or(WholeNumberRuns.one(n(6), null)));
        for (long between = 1; between <= 5; between++) {
            assertFalse(kept.holds(n(between)), "held " + between);
            assertEquals(n(0), kept.greatestAtOrBelow(n(between)));
            assertEquals(n(6), kept.leastAtOrAbove(n(between)));
        }
        assertTrue(kept.holds(n(6)));
        assertEquals(n(0), kept.least());
        assertNull(kept.greatest());
    }

    /** {@code 2·x - c = 0} for any {@code x}: {@code c} is even. */
    @Test
    void whatTwiceANumberLeavesOfTheOneBesideItIsTheEvens() {
        WholeNumberSet cs = WholeNumberSet.EVERY.valuesBeside(n(2), n(-1), n(0));
        assertTrue(cs.holds(n(4)));
        assertTrue(cs.holds(n(-6)));
        assertFalse(cs.holds(n(3)));
        // With weight one, c = x: every number.
        assertTrue(WholeNumberSet.EVERY.valuesBeside(n(1), n(-1), n(0)).holds(n(3)));
    }

    /** {@code x ≥ 6}, twice: {@code c = 2·x} is the even numbers from twelve. */
    @Test
    void theEndsOfTheRunAreCarriedToTheOtherNumber() {
        WholeNumberSet x = WholeNumberSet.ofRuns(WholeNumberRuns.one(n(6), null));
        WholeNumberSet cs = x.valuesBeside(n(2), n(-1), n(0));
        assertEquals(n(12), cs.least());
        assertNull(cs.greatest());
        assertTrue(cs.holds(n(12)));
        assertFalse(cs.holds(n(10)));
        assertFalse(cs.holds(n(13)));
    }

    /** {@code 3·x + 2·c = 7} has solutions {@code x = 1, c = 2} and nothing for even {@code x}. */
    @Test
    void aWeightedEquationLeavesTheClassItsSolutionsAreIn() {
        WholeNumberSet cs = WholeNumberSet.EVERY.valuesBeside(n(3), n(2), n(-7));
        // 2c = 7 - 3x: c is whole where x is odd, and then c runs over every number.
        assertTrue(cs.holds(n(2)));
        assertTrue(cs.holds(n(-1)));
        // A negative weight and a shifted constant: c = 5 - x for x in 0..3.
        WholeNumberSet x = WholeNumberSet.ofRuns(WholeNumberRuns.one(n(0), n(3)));
        WholeNumberSet shifted = x.valuesBeside(n(1), n(1), n(-5));
        assertEquals(n(2), shifted.least());
        assertEquals(n(5), shifted.greatest());
        assertTrue(shifted.holds(n(3)));
        assertFalse(shifted.holds(n(6)));
        // s - c + 5 = 0 for s in 0..3: c = s + 5, from five to eight.
        WholeNumberSet turned = x.valuesBeside(n(1), n(-1), n(5));
        assertEquals(n(5), turned.least());
        assertEquals(n(8), turned.greatest());
    }

    @Test
    void aWeightOfNoughtLeavesNothingToSolve() {
        assertNull(WholeNumberSet.EVERY.valuesBeside(n(0), n(1), n(0)));
        assertNull(WholeNumberSet.EVERY.valuesBeside(n(1), n(0), n(0)));
    }

    @Test
    void aRunWithNoMemberOfTheRemainderHoldsNothing() {
        WholeNumberSet oneToOne = WholeNumberSet.ofRuns(WholeNumberRuns.one(n(1), n(1)))
                .and(evens());
        assertTrue(oneToOne.isNone());
    }
}
