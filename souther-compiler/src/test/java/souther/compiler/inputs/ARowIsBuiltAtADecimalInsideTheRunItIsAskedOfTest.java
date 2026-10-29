package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;

import java.math.BigDecimal;
import java.math.BigInteger;

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

    @Test
    void aRunNarrowerThanTheFewestPlacesAsksIsNoRowAndNeitherIsAnEmptyOne() {
        ExactRatio narrow = A_THIRD.plus(ExactRatio.ONE.dividedBy(
                ExactRatio.of(BigInteger.TEN.pow(60))).orNull()).orNull();
        assertNull(DecimalPoints.within(ExactCut.exclusive(A_THIRD),
                ExactCut.exclusive(narrow), true));
        assertNull(DecimalPoints.within(ExactCut.exclusive(ExactRatio.ONE),
                ExactCut.inclusive(ExactRatio.ONE), true));
    }

    @Test
    void theRowStandsInsideTheRunWhenTheOtherEndIsNear() {
        ExactRatio half = ExactRatio.ONE.dividedBy(ExactRatio.of(2)).orNull();
        ExactRatio inside = DecimalPoints.within(ExactCut.exclusive(A_THIRD),
                ExactCut.exclusive(half), true);
        assertEquals(0, inside.compareTo(ExactRatio.of(new BigDecimal("0.4"))), "" + inside);
    }
}
