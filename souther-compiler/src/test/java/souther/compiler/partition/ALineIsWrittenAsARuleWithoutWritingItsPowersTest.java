package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Towards;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link Seam#asARuleAbout} writes a line as the reduced rule that draws it, and does so at any
 * scale the line's value is held at.
 *
 * <p>Reduced, because two rules drawing one line are one place and the class they part is named
 * once, by whichever of them was read first. Written from the value's parts, because the value is
 * held compactly and its powers can be past what any number the host builds. And where what the
 * line stands over is past what a ratio holds, the line is written against the quantity itself at
 * the value it is — which follows from the value alone, so it too is one spelling per line.
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

    /** No ratio holds what this line stands over, so it has no multiple to be written with. */
    @Test
    void aLineOverMoreThanARatioHoldsIsWrittenAgainstTheQuantityItself() {
        Seam least = lineAt(tenTo(Long.MIN_VALUE), ExactRatio.ONE);

        assertEquals("x <= 1E-9223372036854775808", ruleAbout(least, Towards.BELOW));
        assertEquals("1E-9223372036854775808 < x", ruleAbout(least, Towards.ABOVE));
    }

    @Test
    void twoLinesDrawnInOneMultipleShareIt() {
        Band between = runBetween(lineAt(ExactRatio.of(1), ExactRatio.of(3)),
                lineAt(ExactRatio.of(2), ExactRatio.of(3)));

        assertEquals(ExactRatio.of(3), between.sharedMultiple());
    }

    /** Written against the quantity itself, such a line has no multiple for the run to share. */
    @Test
    void aLineOverMoreThanARatioHoldsSharesNoMultiple() {
        Band between = runBetween(lineAt(tenTo(Long.MIN_VALUE), ExactRatio.ONE),
                lineAt(new ExactRatio(BigInteger.valueOf(3), BigInteger.ONE,
                        Long.MIN_VALUE, Long.MIN_VALUE), ExactRatio.ONE));

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
