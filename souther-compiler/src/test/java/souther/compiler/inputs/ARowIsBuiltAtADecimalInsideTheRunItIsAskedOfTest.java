package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation draws its lines at rational numbers and a row stands at decimals, so a row is built
 * at a decimal inside the run it is asked of, nearest the end it is asked at.
 */
class ARowIsBuiltAtADecimalInsideTheRunItIsAskedOfTest {

    private static final ExactRatio A_THIRD = ExactRatio.ONE.dividedBy(ExactRatio.of(3)).orNull();

    @Test
    void anEndTheRunHoldsAndWhichIsADecimalIsWhereTheRowStands() {
        assertEquals(ExactRatio.of(5),
                DecimalPoints.within(ExactCut.inclusive(ExactRatio.of(5)), null, true));
    }

    @Test
    void anEndTheRunLeavesOutIsPassedByTheFewestPlacesThatPassIt() {
        assertEquals(ExactRatio.ONE,
                DecimalPoints.within(ExactCut.exclusive(ExactRatio.ZERO), null, true));
        assertEquals(ExactRatio.ZERO.minus(ExactRatio.ONE).orNull(),
                DecimalPoints.within(ExactCut.exclusive(ExactRatio.ZERO), null, false));
    }

    @Test
    void anEndNoDecimalWritesIsNeverWhereARowStandsWhetherTheRunHoldsItOrNot() {
        for (boolean inclusive : new boolean[] {true, false}) {
            ExactCut third = new ExactCut(A_THIRD, inclusive);
            ExactRatio above = DecimalPoints.within(third, ExactCut.inclusive(ExactRatio.ONE),
                    true);
            ExactRatio below = DecimalPoints.within(third, ExactCut.inclusive(ExactRatio.ZERO),
                    false);
            assertNotNull(above);
            assertNotNull(below);
            assertTrue(above.fitsWrittenDecimal() && above.compareTo(A_THIRD) > 0
                    && above.compareTo(ExactRatio.ONE) <= 0, "above: " + above);
            assertTrue(below.fitsWrittenDecimal() && below.compareTo(A_THIRD) < 0
                    && below.compareTo(ExactRatio.ZERO) >= 0, "below: " + below);
        }
    }

    /** The run is inside both its ends, and the row is a decimal. */
    private static void assertStandsInside(ExactRatio row, ExactCut lower, ExactCut upper) {
        assertNotNull(row);
        assertTrue(row.fitsWrittenDecimal(), "a decimal: " + row);
        assertTrue(row.compareTo(lower.at()) > 0 || (lower.inclusive()
                && row.compareTo(lower.at()) == 0), "above " + lower + ": " + row);
        assertTrue(row.compareTo(upper.at()) < 0 || (upper.inclusive()
                && row.compareTo(upper.at()) == 0), "below " + upper + ": " + row);
    }

    @Test
    void aRunNarrowerThanAnyFixedNumberOfPlacesStillHasARowBuiltInIt() {
        for (int places : new int[] {61, 200, 5000}) {
            ExactCut lower = ExactCut.exclusive(A_THIRD);
            ExactCut upper = ExactCut.exclusive(A_THIRD.plus(ExactRatio.ONE.dividedBy(
                    ExactRatio.of(BigInteger.TEN.pow(places))).orNull()).orNull());
            assertStandsInside(DecimalPoints.within(lower, upper, true), lower, upper);
            assertStandsInside(DecimalPoints.within(upper, lower, false), lower, upper);
        }
    }

    @Test
    void aRunWithNothingInsideIsNoRowAndNeitherIsOneNeededMorePlacesThanAClaimIsMadeOf() {
        assertNull(DecimalPoints.within(ExactCut.exclusive(ExactRatio.ONE),
                ExactCut.inclusive(ExactRatio.ONE), true));
        ExactCut lower = ExactCut.exclusive(A_THIRD);
        ExactCut tooNarrow = ExactCut.exclusive(A_THIRD.plus(ExactRatio.ONE.dividedBy(
                ExactRatio.of(BigInteger.TEN.pow(DecimalOperation.PLACES_A_CLAIM_IS_MADE_OF + 5)))
                .orNull()).orNull());
        assertNull(DecimalPoints.within(lower, tooNarrow, true));
    }

    @Test
    void theRowStandsInsideTheRunWhateverTheWidthBetweenItsEnds() {
        ExactRatio half = ExactRatio.ONE.dividedBy(ExactRatio.of(2)).orNull();
        ExactCut lower = ExactCut.exclusive(A_THIRD);
        ExactCut upper = ExactCut.exclusive(half);
        assertStandsInside(DecimalPoints.within(lower, upper, true), lower, upper);
        assertStandsInside(DecimalPoints.within(upper, lower, false), lower, upper);
    }

    /** A term held to a tenth to two tenths has no row beside a third in the run it lies past: the
     *  one below is the greatest it holds, and none lies above. */
    @Test
    void theRowsBesideALineAreInsideTheRunTheTermHolds() {
        ExactCut tenth = ExactCut.inclusive(ExactRatio.of(new BigDecimal("0.1")));
        ExactCut fifth = ExactCut.inclusive(ExactRatio.of(new BigDecimal("0.2")));
        assertEquals(List.of(ExactRatio.of(new BigDecimal("0.2"))),
                DecimalPoints.besideTheLine(A_THIRD, tenth, fifth));
        ExactCut nought = ExactCut.inclusive(ExactRatio.ZERO);
        ExactCut one = ExactCut.inclusive(ExactRatio.ONE);
        List<ExactRatio> both = DecimalPoints.besideTheLine(A_THIRD, nought, one);
        assertEquals(2, both.size());
        assertStandsInside(both.get(0), nought, ExactCut.exclusive(A_THIRD));
        assertStandsInside(both.get(1), ExactCut.exclusive(A_THIRD), one);
    }
}
