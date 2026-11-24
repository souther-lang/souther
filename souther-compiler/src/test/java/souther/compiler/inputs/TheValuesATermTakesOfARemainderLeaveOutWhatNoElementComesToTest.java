package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.numeric.WholeNumberSet;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a term is shown to take of the values it may take is asked of one owner: a value is taken
 * only where the set shown says so, and the run those values end at is the run read beside a line.
 */
class TheValuesATermTakesOfARemainderLeaveOutWhatNoElementComesToTest {

    private static BigInteger n(long value) {
        return BigInteger.valueOf(value);
    }

    private static WholeNumberSet evens() {
        return WholeNumberSet.ofClass(new Congruences(BigInteger.ZERO, n(2)));
    }

    private static WholeNumberSet from(long least) {
        return WholeNumberSet.ofRuns(WholeNumberRuns.one(n(least), null));
    }

    @Test
    void theEvenNumbersFromNoughtTakeNoOddOneAndNothingBelow() {
        WhatARelationLeavesUndivided.Term.Stepped stepped =
                new WhatARelationLeavesUndivided.Term.Stepped(evens().and(from(0)), evens());
        assertTrue(stepped.takes(n(4)));
        assertFalse(stepped.takes(n(3)));
        assertFalse(stepped.takes(n(-4)));
        assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.ZERO), null),
                stepped.hull());
    }

    /** What a filter keeping six or more is shown to total: nought, or six and more. */
    @Test
    void aStretchBetweenNoughtAndTheLeastKeptIsTakenByNone() {
        WholeNumberSet noughtAlone = WholeNumberSet.ofRuns(WholeNumberRuns.one(BigInteger.ZERO,
                BigInteger.ZERO));
        WhatARelationLeavesUndivided.Term.Stepped stepped =
                new WhatARelationLeavesUndivided.Term.Stepped(noughtAlone.or(from(6)),
                        noughtAlone.or(from(6)));
        assertTrue(stepped.takes(n(0)));
        for (long inside = 1; inside <= 5; inside++) {
            assertFalse(stepped.takes(n(inside)), "inside " + inside);
        }
        assertTrue(stepped.takes(n(6)));
        assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.ZERO), null),
                stepped.hull());
    }

    /** A term takes some value, and lies somewhere. */
    @Test
    void aSteppedTermTakesAValue() {
        assertThrows(IllegalArgumentException.class,
                () -> new WhatARelationLeavesUndivided.Term.Stepped(WholeNumberSet.NONE,
                        evens()));
        assertThrows(IllegalArgumentException.class,
                () -> new WhatARelationLeavesUndivided.Term.Stepped(evens(),
                        WholeNumberSet.NONE));
    }

    @Test
    void theHullOfAClosedRunHasBothEndsTaken() {
        WhatARelationLeavesUndivided.Term.Stepped stepped =
                new WhatARelationLeavesUndivided.Term.Stepped(evens().and(WholeNumberSet.ofRuns(
                        WholeNumberRuns.one(n(1), n(11)))), evens());
        assertEquals(new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(new BigDecimal(2))),
                Endpoint.inclusive(Count.of(new BigDecimal(10)))), stepped.hull());
    }
}
