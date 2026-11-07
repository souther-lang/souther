package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.abort.GetsPast;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.WhereAnOperatorAnswers;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every value a count moves to under a key is {@code first + step * k} for the {@code k} elements
 * before it that have the key, fewer than a collection holds: so the moves stay within what an
 * {@code Int} holds exactly where the last of them does, which is one element short of
 * {@link GetsPast#MOST_ELEMENTS}.
 *
 * <p>Each case sits on one side of that end, worked out from the ends of an {@code Int} and the
 * most a collection holds rather than written down, so a law reading {@code k} up to the most a
 * collection holds is told apart from this one in both directions a count moves.
 */
class WhatACountMovesToLiesWithinItsOperatorTest {

    private static final BigInteger LEAST = WhereAnOperatorAnswers.WHAT_AN_INT_HOLDS.least();
    private static final BigInteger GREATEST = WhereAnOperatorAnswers.WHAT_AN_INT_HOLDS.greatest();
    private static final BigInteger MOST_BEFORE = GetsPast.MOST_ELEMENTS.subtract(BigInteger.ONE);

    private static boolean within(BigInteger first, BigInteger step) {
        return new KeyedAccumulation.Filed.Counted(ExactRatio.of(first), ExactRatio.of(step))
                .everyValueMovedLiesWithin(LEAST, GREATEST);
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
