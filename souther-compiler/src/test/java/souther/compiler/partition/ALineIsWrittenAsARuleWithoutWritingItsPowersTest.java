package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.Carrier;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Towards;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link Seam#asARuleAbout} writes a line as the reduced rule that draws it, and does so at any
 * scale the line's value is held at.
 *
 * <p>Reduced, because two rules drawing one line are one place and the class they part is named
 * once, by whichever of them was read first. Written from the value's parts, because the value is
 * held compactly and its powers can be past what any number the host builds. And read off the same
 * terms the position is compared as, so a line that can be named is one the arrangement can hold.
 */
class ALineIsWrittenAsARuleWithoutWritingItsPowersTest {

    private static final long FAR = 1L << 32;

    /** How the class labels write so much of the quantity. */
    private static String much(ExactRatio by) {
        return by.equals(ExactRatio.ONE) ? "x" : by.spelled() + " * x";
    }

    private static String ruleAbout(Seam line, Towards side) {
        return line.asARuleAbout(ALineIsWrittenAsARuleWithoutWritingItsPowersTest::much, side);
    }

    private static Seam lineAt(ExactRatio written, ExactRatio per) {
        return new Seam(new CutPosition(new Level.OfTheQuantity(written), per), null, null);
    }

    private static ExactRatio tenTo(long exponent) {
        return new ExactRatio(BigInteger.ONE, BigInteger.ONE, exponent, exponent);
    }

    @Test
    void twoRulesDrawingOneLineWriteItOneWay() {
        Seam third = lineAt(ExactRatio.of(1), ExactRatio.of(3));
        Seam twoSixths = lineAt(ExactRatio.of(2), ExactRatio.of(6));

        assertEquals("3 * x <= 1", ruleAbout(third, Towards.BELOW));
        assertEquals(ruleAbout(third, Towards.BELOW), ruleAbout(twoSixths, Towards.BELOW));
    }

    @Test
    void aLineAtAFineDecimalIsWrittenWithoutItsDigits() {
        Seam fine = lineAt(tenTo(-FAR), ExactRatio.ONE);

        assertEquals("1E+4294967296 * x <= 1", ruleAbout(fine, Towards.BELOW));
        assertEquals("1 < 1E+4294967296 * x", ruleAbout(fine, Towards.ABOVE));
    }

    /**
     * A line at the least exponent stands over a power one past any exponent, so its multiple stops
     * at the greatest one and what it comes to keeps the tenth left over.
     */
    @Test
    void aLineAtTheLeastExponentIsWrittenInTheTermsARatioHolds() {
        Seam least = lineAt(tenTo(Long.MIN_VALUE), ExactRatio.ONE);

        assertEquals("1E+9223372036854775807 * x <= 0.1", ruleAbout(least, Towards.BELOW));
        assertEquals("0.1 < 1E+9223372036854775807 * x", ruleAbout(least, Towards.ABOVE));
    }

    /**
     * The same line through the arrangement, which holds every end the way a report compares it
     * before any of them is named — so a line that could be named but not compared would never reach
     * its name.
     */
    @Test
    void anArrangementOverALineAtTheLeastExponentIsBuiltAndItsRunsNamed() {
        Carrier dense = new Carrier.Dense();
        Seam least = HeldSeams.of(
                LevelSpace.overFiniteDecimals(LevelSpace.generatorOverFiniteDecimals(ExactRatio.ONE)),
                new Level.OfTheQuantity(tenTo(Long.MIN_VALUE)), Towards.BELOW,
                new Seam.Scale(ExactRatio.ONE, dense));

        QuantityArrangement arranged = QuantityArrangement.of(LevelSpace.onACarrier(dense),
                List.of(Parting.by(least, WhatTheRulesTogetherLeaveAQuantityTest.aLine(0))));

        assertEquals(2, arranged.runs().size(), "one line, a run either side of it");
        Seam parted = arranged.partings().get(0).geometry();
        assertEquals(ruleAbout(least, Towards.BELOW), ruleAbout(parted, Towards.BELOW));
        assertEquals(ruleAbout(parted.canonical(), Towards.BELOW), ruleAbout(parted, Towards.BELOW),
                "and the line it is compared as is named as the line it is");
    }

    @Test
    void twoLinesDrawnInOneMultipleShareIt() {
        Band between = runBetween(lineAt(ExactRatio.of(1), ExactRatio.of(3)),
                lineAt(ExactRatio.of(2), ExactRatio.of(3)));

        assertEquals(ExactRatio.of(3), between.sharedMultiple());
    }

    /** Two lines at the least exponent are written per the same multiple, and a run between them
     *  says it once. */
    @Test
    void twoLinesAtTheLeastExponentShareTheirMultiple() {
        Band between = runBetween(lineAt(tenTo(Long.MIN_VALUE), ExactRatio.ONE),
                lineAt(new ExactRatio(BigInteger.valueOf(3), BigInteger.ONE,
                        Long.MIN_VALUE, Long.MIN_VALUE), ExactRatio.ONE));

        assertEquals(tenTo(Long.MAX_VALUE), between.sharedMultiple());
    }

    @Test
    void twoLinesDrawnInDifferentMultiplesShareNone() {
        Band between = runBetween(lineAt(ExactRatio.of(1), ExactRatio.of(3)),
                lineAt(ExactRatio.of(1), ExactRatio.of(7)));

        assertNull(between.sharedMultiple());
    }

    private static Band runBetween(Seam under, Seam over) {
        return new Band(Band.endAt(under, null, Towards.ABOVE), Band.endAt(over, null, Towards.BELOW));
    }

    /** A record holding a level prints it without being asked, and prints it within bounds. */
    @Test
    void whatHoldsAFineLevelPrintsIt() {
        Level fine = new Level.OfTheQuantity(tenTo(-FAR));
        String said = new PointAnswer.AtLine(new Criterion.AtTheLevel(fine)).toString();

        assertTrue(said.contains("1E-4294967296"), said);
        assertTrue(said.length() < 200, said);
    }
}
