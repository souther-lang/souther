package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A ratio at the least sixty-four-bit exponent is held, and what needs its negation is what refuses.
 *
 * <p>That a value is held and that an operation on it has an answer are two questions. The least long
 * has no positive counterpart, so a reciprocal of it, and the part of it below the line, has no exponent
 * to be; but the value itself, a quotient of it by itself, the order it stands in and the residue of its
 * power are all answers a ratio has, and none of them is refused for the sake of a step that would have
 * negated it.
 */
class TheLeastExponentIsAValueLikeAnyOtherTest {

    private static ExactRatio atTheLeastTwos() {
        ExactRatio at = new ExactRatio(BigInteger.ONE, BigInteger.ONE, Long.MIN_VALUE, 0);
        assertEquals(Long.MIN_VALUE, at.twos(), "the value this is about");
        return at;
    }

    @Test
    void aValueAtTheLeastExponentIsHeld() {
        ExactRatio at = atTheLeastTwos();

        assertEquals(at, new ExactRatio(BigInteger.ONE, BigInteger.ONE, Long.MIN_VALUE, 0));
        assertTrue(at.terminates());
    }

    @Test
    void aValueDividedByItselfIsOne() {
        ExactRatio at = atTheLeastTwos();

        assertEquals(ExactAnswer.held(ExactRatio.ONE), at.dividedBy(at));
    }

    @Test
    void aProductPastTheRangeSaysItHasNoRepresentation() {
        ExactRatio at = atTheLeastTwos();

        assertEquals(ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS), at.times(at));
    }

    @Test
    void aQuotientPastTheRangeSaysItHasNoRepresentation() {
        ExactRatio at = atTheLeastTwos();

        assertEquals(ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS),
                ExactRatio.ONE.dividedBy(at));
    }

    /** What it stands over has an exponent no long holds, and the product with it does. */
    @Test
    void aValueTimesWhatAnotherStandsOverIsHeldWhereThatDenominatorAloneIsNot() {
        ExactRatio at = atTheLeastTwos();

        assertEquals(ExactAnswer.held(ExactRatio.ONE), at.timesWhatItStandsOver(at));
        assertEquals(ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS),
                ExactRatio.ONE.timesWhatItStandsOver(at));
    }

    @Test
    void wholenessAndDecimalnessAreAskedWithoutTheQuotientBeingHeld() {
        ExactRatio at = atTheLeastTwos();

        assertTrue(ExactRatio.ONE.isWholeMultipleOf(at));
        assertTrue(ExactRatio.ONE.isWrittenDecimalMultipleOf(at));
        assertFalse(at.isWholeMultipleOf(ExactRatio.ONE));
        assertFalse(at.isWrittenDecimalMultipleOf(ExactRatio.ONE));
    }

    @Test
    void aValueAtTheLeastExponentIsOrdered() {
        ExactRatio at = atTheLeastTwos();

        assertTrue(at.compareTo(ExactRatio.ONE) < 0);
        assertTrue(ExactRatio.ONE.compareTo(at) > 0);
        assertTrue(at.compareTo(new ExactRatio(BigInteger.ONE, BigInteger.ONE, Long.MIN_VALUE + 1, 0)) < 0);
        assertEquals(0, at.compareTo(atTheLeastTwos()));
    }

    /** The power is a residue and not a number, so the residue is the one the exponent's true size gives. */
    @Test
    void theResidueOfItsPowerBelowTheLineIsTheOneItsTrueSizeGives() {
        BigInteger modulus = BigInteger.valueOf(7);
        BigInteger exponent = BigInteger.ONE.shiftLeft(63);

        assertEquals(BigInteger.TWO.modPow(exponent, modulus), atTheLeastTwos().denominatorMod(modulus));
        assertEquals(BigInteger.ONE, atTheLeastTwos().numeratorMod(modulus));
    }

    @Test
    void whatWouldNeedItsNegationAsAnExponentRefuses() {
        ExactRatio at = atTheLeastTwos();

        assertThrows(ArithmeticException.class, at::asFraction);
    }

    /**
     * A rule writes it all the same: per the greatest power there is, coming to the one two left
     * over. The terms are the value, and what it is written per is whole and above nought.
     */
    @Test
    void aValueAtTheLeastExponentHasTermsARuleWritesItIn() {
        ExactRatio at = atTheLeastTwos();
        ExactRatio.Terms terms = at.asTerms();

        assertEquals(new ExactRatio(BigInteger.ONE, BigInteger.ONE, Long.MAX_VALUE, 0), terms.per());
        assertEquals(new ExactRatio(BigInteger.ONE, BigInteger.ONE, -1, 0), terms.comesTo());
        assertEquals(ExactAnswer.held(at), terms.comesTo().dividedBy(terms.per()));
    }

    /** Anywhere else the terms are the lowest ones, both whole. */
    @Test
    void aValueAwayFromTheLeastExponentHasItsLowestTerms() {
        ExactRatio.Terms twoSixths = ExactRatio.of(BigInteger.TWO, BigInteger.valueOf(6)).asTerms();
        ExactRatio.Terms fiveHalves = ExactRatio.of(BigInteger.valueOf(5), BigInteger.TWO).asTerms();

        assertEquals(new ExactRatio.Terms(ExactRatio.ONE, ExactRatio.of(3)), twoSixths);
        assertEquals(new ExactRatio.Terms(ExactRatio.of(5), ExactRatio.of(2)), fiveHalves);
    }

    /** A decimal's scale is thirty-two bits, so a value this far below it is no decimal a model writes. */
    @Test
    void aValueAtTheLeastExponentIsNoDecimalAModelWrites() {
        ExactRatio at = new ExactRatio(BigInteger.ONE, BigInteger.ONE, Long.MIN_VALUE, Long.MIN_VALUE);

        assertTrue(at.terminates());
        assertFalse(at.fitsWrittenDecimal());
        assertNull(at.asWrittenDecimal());
    }
}
