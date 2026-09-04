package souther.compiler.check;

import souther.runtime.ConstraintViolation;
import souther.runtime.DecimalMath;
import souther.runtime.HALF_UP;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The scales a division runs at are one range, and the check and the run time answer it separately
 * (ADR-0112). The specification states it; neither implementation reads the other, so what holds
 * them together is this — asked at the ends, where they would part company first.
 *
 * <p>Sharing a constant would be the other way to keep them equal, and it would tie the analysis to
 * whichever backend is linked. What the analysis is about is the language.
 */
class OneScaleRangeIsReadByTheCheckAndByTheRunTimeTest {

    /** The ends, and one step past each. */
    private static final long[] ENDS = {
        (long) Integer.MIN_VALUE - 1, Integer.MIN_VALUE, Integer.MAX_VALUE, (long) Integer.MAX_VALUE + 1,
    };

    /** Whether the run time took the scale as the number it is. It aborts either way at these ends —
     *  a division at {@code Integer.MAX_VALUE} has no result a Decimal holds — so what separates the
     *  two is which failure it names, not whether there is one. */
    private static boolean theRunTimeReceives(long scale) {
        ConstraintViolation raised = assertThrows(ConstraintViolation.class,
                () -> DecimalMath.divide(BigDecimal.ONE, new BigDecimal("3"), scale,
                        HALF_UP.INSTANCE));
        return !raised.getMessage().contains("scale is outside the range the run time takes");
    }

    @Test
    void theTwoAgreeAtEveryEndOfTheRange() {
        for (long scale : ENDS) {
            boolean checkReads = ScaleRange.receivedUnchanged(BigDecimal.valueOf(scale)) != null;
            assertEquals(theRunTimeReceives(scale), checkReads,
                    "the check and the run time disagree about scale " + scale);
        }
    }

    @Test
    void theCheckReadsTheEndsAndNothingPastThem() {
        assertNotNull(ScaleRange.receivedUnchanged(BigDecimal.valueOf(Integer.MIN_VALUE)));
        assertNotNull(ScaleRange.receivedUnchanged(BigDecimal.valueOf(Integer.MAX_VALUE)));
        assertNull(ScaleRange.receivedUnchanged(BigDecimal.valueOf((long) Integer.MIN_VALUE - 1)));
        assertNull(ScaleRange.receivedUnchanged(BigDecimal.valueOf((long) Integer.MAX_VALUE + 1)));
        // 2 + 2^32, which a raw narrowing reads as the scale 2 a model might have written.
        assertNull(ScaleRange.receivedUnchanged(BigDecimal.valueOf(4294967298L)));
    }

    /**
     * What a reading will lay a grid out at is a different question and a much smaller number, so
     * the range above is not reachable through a reading at the limit a compilation sets. The two
     * are separate on purpose: one is what the language says a division does, the other is what a
     * compilation is prepared to spend (ADR-0112). Held apart here so that raising the budget can
     * never be read as widening the range, or lowering it as narrowing it.
     */
    @Test
    void theReadingBudgetIsNotTheRange() {
        ReadingPolicy policy = new ReadingPolicy(64, 1000,
                souther.compiler.values.AsACompilationAllows.admittedValues());
        assertEquals(true, policy.laysOutAGridAt(1000));
        assertEquals(false, policy.laysOutAGridAt(1001));
        // Both ends of the range are numbers the run time receives and no reading lays out.
        assertNotNull(ScaleRange.receivedUnchanged(BigDecimal.valueOf(Integer.MAX_VALUE)));
        assertEquals(false, policy.laysOutAGridAt(Integer.MAX_VALUE));
        assertEquals(false, policy.laysOutAGridAt(Integer.MIN_VALUE));
    }
}
