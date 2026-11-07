package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.abort.GetsPast;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.WhereAnOperatorAnswers;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every value a count finds under a key is {@code first + step * (k - 1)} for the {@code k}
 * elements before it that have the key, one at least and fewer than a collection holds: so what
 * is found lies from {@code first} to {@code first + step * (MOST_ELEMENTS - 2)}, and the move
 * {@code n + step} stays within what an {@code Int} holds exactly where the last of those does.
 *
 * <p>Each case sits on one side of that end, worked out from the ends of an {@code Int} and the
 * most a collection holds rather than written down, so a law reading {@code k} up to the most a
 * collection holds is told apart from this one in both directions a count moves.
 */
class WhatACountMovesToLiesWithinItsOperatorTest {

    private static final BigInteger LEAST = WhereAnOperatorAnswers.WHAT_AN_INT_HOLDS.least();
    private static final BigInteger GREATEST = WhereAnOperatorAnswers.WHAT_AN_INT_HOLDS.greatest();
    private static final BigInteger MOST_BEFORE = GetsPast.MOST_ELEMENTS.subtract(BigInteger.ONE);

    /** Whether the move by {@code step} of every value found lies within an {@code Int}. */
    private static boolean within(BigInteger first, BigInteger step) {
        List<ExactRatio> ends = new KeyedAccumulation.Filed.Counted(ExactRatio.of(first),
                ExactRatio.of(step)).endsOfWhatIsFound();
        ExactRatio least = ends.getFirst().plus(ExactRatio.of(step)).orNull();
        ExactRatio greatest = ends.getLast().plus(ExactRatio.of(step)).orNull();
        return least.compareTo(ExactRatio.of(LEAST)) >= 0
                && greatest.compareTo(ExactRatio.of(GREATEST)) <= 0;
    }

    @Test
    void whatACountByOneFindsIsFromOneToTheElementsBeforeTheLastOfAFullCollection() {
        assertEquals(List.of(ExactRatio.ONE, ExactRatio.of(MOST_BEFORE)),
                new KeyedAccumulation.Filed.Counted(ExactRatio.ONE, ExactRatio.ONE)
                        .endsOfWhatIsFound());
    }

    @Test
    void aCountDownFindsTheLesserEndFirst() {
        List<ExactRatio> ends = new KeyedAccumulation.Filed.Counted(ExactRatio.ONE,
                ExactRatio.of(-1)).endsOfWhatIsFound();
        assertTrue(ends.getFirst().compareTo(ends.getLast()) <= 0);
        assertEquals(ExactRatio.ONE, ends.getLast());
    }

    @Test
    void aCountByOneStaysWithinAnInt() {
        assertTrue(within(BigInteger.ONE, BigInteger.ONE));
    }

    @Test
    void theLargestStepFromOneTakesTheLastElementOfAFullCollectionToTheLargestInt() {
        BigInteger step = GREATEST.subtract(BigInteger.ONE).divide(MOST_BEFORE);
        assertTrue(within(BigInteger.ONE, step));
        assertFalse(within(BigInteger.ONE, step.add(BigInteger.ONE)),
                "one more passes the largest Int at the last element of a full collection");
    }

    @Test
    void theLargestFirstValueIsAsManyBelowTheLargestIntAsElementsMayComeBefore() {
        BigInteger first = GREATEST.subtract(MOST_BEFORE);
        assertTrue(within(first, BigInteger.ONE));
        assertFalse(within(first.add(BigInteger.ONE), BigInteger.ONE));
    }

    @Test
    void aCountDownIsHeldAtTheLeastInt() {
        BigInteger first = LEAST.add(MOST_BEFORE);
        assertTrue(within(first, BigInteger.ONE.negate()));
        assertFalse(within(first.subtract(BigInteger.ONE), BigInteger.ONE.negate()));
    }
}
