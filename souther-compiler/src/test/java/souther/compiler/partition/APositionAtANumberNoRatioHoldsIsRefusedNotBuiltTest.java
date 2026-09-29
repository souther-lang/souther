package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.UnheldNumber;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line is placed at a number, and where that number has no representation the line has no place —
 * which is said as a refusal where positions are made, and not as a number a reader is later handed
 * and cannot take.
 *
 * <p>The exponents a ratio holds end at the least long, and a position divided or scaled by how much
 * of the quantity a rule wrote can pass it from a number that is itself held.
 */
class APositionAtANumberNoRatioHoldsIsRefusedNotBuiltTest {

    private static ExactRatio twoTo(long exponent) {
        return new ExactRatio(BigInteger.ONE, BigInteger.ONE, exponent, 0);
    }

    private static Level.OfTheQuantity at(ExactRatio number) {
        return new Level.OfTheQuantity(number);
    }

    @Test
    void aLineDividedPastTheLeastExponentDoesNotFallAtAHeldNumber() {
        assertFalse(CutPosition.holdsWhereItFalls(at(ExactRatio.ONE), twoTo(Long.MIN_VALUE)),
                "one over the least exponent is a number past the greatest one");
    }

    @Test
    void aLineDividedByItselfFallsAtOne() {
        assertTrue(CutPosition.holdsWhereItFalls(at(twoTo(Long.MIN_VALUE)), twoTo(Long.MIN_VALUE)),
                "the quotient is the difference of two exponents held, and not a reciprocal");
    }

    @Test
    void aPositionScaledPastTheLeastExponentIsRefused() {
        CutPosition line = CutPosition.at(at(twoTo(Long.MIN_VALUE)));

        assertEquals(ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS),
                line.times(twoTo(-1)));
        assertTrue(line.times(twoTo(1)).isHeld());
    }

    @Test
    void aSeamScaledPastTheLeastExponentIsRefused() {
        Seam seam = new Seam(CutPosition.at(at(twoTo(Long.MIN_VALUE))), null, null);

        assertEquals(ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS),
                seam.scaledBy(twoTo(-1)));
        assertTrue(seam.scaledBy(twoTo(1)).isHeld());
    }

    @Test
    void aPartingScaledPastTheLeastExponentIsRefused() {
        Parting parting = Parting.by(
                new Seam(CutPosition.at(at(twoTo(Long.MIN_VALUE))), null, null),
                WhatTheRulesTogetherLeaveAQuantityTest.aLine(0));

        assertEquals(ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS),
                parting.scaledBy(twoTo(-1)));
        assertTrue(parting.scaledBy(twoTo(1)).isHeld());
    }
}
