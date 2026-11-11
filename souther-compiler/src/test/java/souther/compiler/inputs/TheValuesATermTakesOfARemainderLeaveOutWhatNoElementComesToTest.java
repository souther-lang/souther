package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a term takes of a remainder, with a stretch taken by none, is asked of one owner: a value
 * is taken only of the remainder and outside the stretch, and the nearest values on either side of
 * a line are values taken, so a row stood at them is a row the term has.
 */
class TheValuesATermTakesOfARemainderLeaveOutWhatNoElementComesToTest {

    private static BigInteger n(long value) {
        return BigInteger.valueOf(value);
    }

    private static NumericDomain.Bounds from(long least) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(new BigDecimal(least))), null);
    }

    @Test
    void theEvenNumbersTakeNoOddOne() {
        WhatARelationLeavesUndivided.Term.Stepped evens =
                new WhatARelationLeavesUndivided.Term.Stepped(from(0),
                        new Congruences(BigInteger.ZERO, n(2)));
        assertTrue(evens.takesOfTheRemainder(n(4)));
        assertFalse(evens.takesOfTheRemainder(n(3)));
        assertEquals(n(2), evens.takenAtOrBelow(n(3)));
        assertEquals(n(4), evens.takenAtOrAbove(n(3)));
        assertEquals(n(-4), evens.takenAtOrBelow(n(-3)));
    }

    /** What a filter keeps from six on and leaves out otherwise totals nought or six and more. */
    @Test
    void aStretchBetweenNoughtAndTheLeastKeptIsTakenByNone() {
        WhatARelationLeavesUndivided.Term.Stepped kept =
                new WhatARelationLeavesUndivided.Term.Stepped(from(0),
                        new Congruences(BigInteger.ZERO, BigInteger.ONE), n(1), n(5), true);
        assertTrue(kept.takesOfTheRemainder(n(0)));
        for (long inside = 1; inside <= 5; inside++) {
            assertFalse(kept.takesOfTheRemainder(n(inside)), "inside " + inside);
            assertEquals(n(0), kept.takenAtOrBelow(n(inside)), "below " + inside);
            assertEquals(n(6), kept.takenAtOrAbove(n(inside)), "above " + inside);
        }
        assertTrue(kept.takesOfTheRemainder(n(6)));
        assertEquals(n(7), kept.takenAtOrAbove(n(7)));
    }

    @Test
    void aStretchHasItsEndsInOrder() {
        try {
            new WhatARelationLeavesUndivided.Term.Stepped(from(0),
                    new Congruences(BigInteger.ZERO, BigInteger.ONE), n(5), n(1), true);
        } catch (IllegalArgumentException expected) {
            return;
        }
        throw new AssertionError("a stretch with its ends out of order was made");
    }
}
