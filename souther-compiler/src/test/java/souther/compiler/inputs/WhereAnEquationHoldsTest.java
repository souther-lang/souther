package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.numeric.WholeNumberSet;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An equation of a number beside a weighed one holds at the values the weighing can reach, and no
 * other: what is shown reached and what may be reached are told apart.
 */
class WhereAnEquationHoldsTest {

    private static BigInteger n(long value) {
        return BigInteger.valueOf(value);
    }

    private static WholeNumberSet from(long least) {
        return WholeNumberSet.ofRuns(WholeNumberRuns.one(n(least), null));
    }

    /** {@code x * 2 == cap} for any {@code x}: an even {@code cap} is held and an odd one fails. */
    @Test
    void twiceANumberHoldsAtTheEvenValuesAndFailsAtTheOdd() {
        WhereAnEquationHolds at = WhereAnEquationHolds.of(WholeNumberSet.EVERY,
                WholeNumberSet.EVERY, n(2), n(-1), n(0));
        assertTrue(at.isShownToHoldAt(n(10)));
        assertTrue(at.isShownToHoldAt(n(-4)));
        assertFalse(at.isShownToHoldAt(n(7)));
        assertTrue(at.failsAt(n(7)));
        assertFalse(at.failsAt(n(10)));
    }

    /** A weight of one reaches every value, so none fails. */
    @Test
    void aNumberBesideItselfHoldsAtEveryValue() {
        WhereAnEquationHolds at = WhereAnEquationHolds.of(WholeNumberSet.EVERY,
                WholeNumberSet.EVERY, n(1), n(-1), n(0));
        assertTrue(at.isShownToHoldAt(n(7)));
        assertFalse(at.failsAt(n(-7)));
    }

    /**
     * What a filter keeping six or more totals: nought, or six and more shown by one element, and
     * nought or one and more where the elements may be several. {@code total == cap} holds at
     * nought and from six, and fails nowhere a total may come to be.
     */
    @Test
    void aTotalOverAFilterIsShownReachedAtNoughtAndFromSixAndNotBetween() {
        WholeNumberSet noughtAlone = WholeNumberSet.ofRuns(WholeNumberRuns.one(BigInteger.ZERO,
                BigInteger.ZERO));
        WholeNumberSet shownTaken = noughtAlone.or(from(6));
        WhereAnEquationHolds at = WhereAnEquationHolds.of(shownTaken, shownTaken, n(1), n(-1),
                n(0));
        assertTrue(at.isShownToHoldAt(n(0)));
        assertTrue(at.isShownToHoldAt(n(6)));
        for (long between = 1; between <= 5; between++) {
            assertFalse(at.isShownToHoldAt(n(between)), "shown at " + between);
            assertTrue(at.failsAt(n(between)), "fails at " + between);
        }
        assertTrue(at.failsAt(n(-1)));
    }

    /**
     * Where a value is shown to be taken by one element and the totals of several elements may
     * take more, a value past what one shows is not said to fail.
     */
    @Test
    void aValueOnlySeveralElementsMayReachIsNeitherShownNorFailing() {
        WholeNumberSet evens = WholeNumberSet.ofClass(new Congruences(BigInteger.ZERO, n(2)));
        WholeNumberSet oneElement = evens.and(WholeNumberSet.ofRuns(WholeNumberRuns.one(
                BigInteger.ZERO, n(20))));
        WhereAnEquationHolds at = WhereAnEquationHolds.of(oneElement, evens, n(1), n(-1), n(0));
        assertTrue(at.isShownToHoldAt(n(20)));
        assertFalse(at.isShownToHoldAt(n(24)));
        assertFalse(at.failsAt(n(24)));
        assertTrue(at.failsAt(n(23)));
    }

    @Test
    void aWeightOfNoughtIsNoRelationOfTheTwo() {
        assertNull(WhereAnEquationHolds.of(WholeNumberSet.EVERY, WholeNumberSet.EVERY, n(0), n(1),
                n(0)));
    }
}
