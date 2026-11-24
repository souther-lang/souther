package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A value a run holds, picked to stand a term at: nought where the run holds it, and otherwise
 * the value nearest the end on nought's side — the end where the run holds it, and a step inside
 * an end it leaves out, a whole number for whole numbers and a decimal for decimals.
 */
class AValueARunHoldsIsPickedInsideTheEndsItLeavesOutTest {

    private static Endpoint at(String number, boolean inclusive) {
        Count count = Count.of(new BigDecimal(number));
        return inclusive ? Endpoint.inclusive(count) : Endpoint.exclusive(count);
    }

    private static ExactRatio number(String written) {
        return Count.of(new BigDecimal(written)).exactly();
    }

    /** Above an end it leaves out and running on, a decimal is held one past it; whole numbers
     *  the whole number past it. */
    @Test
    void anEndLeftOutIsPassedByAStepInward() {
        NumericDomain.Bounds aboveTheCap = new NumericDomain.Bounds(at("150000", false), null);
        assertEquals(number("150001"), aboveTheCap.aValueNearestNought(Granularity.DENSE));
        assertEquals(number("150001"), aboveTheCap.aValueNearestNought(Granularity.DISCRETE));
    }

    /** Between two ends nearer each other than one, a decimal is held halfway; whole numbers
     *  between them there are none of. */
    @Test
    void endsNearerThanOneAreMetHalfway() {
        NumericDomain.Bounds narrow =
                new NumericDomain.Bounds(at("0.5", false), at("0.6", false));
        assertEquals(number("0.55"), narrow.aValueNearestNought(Granularity.DENSE));
        assertNull(narrow.aValueNearestNought(Granularity.DISCRETE));
    }

    /** Below nought the end on nought's side is the greatest, and an end the run holds is
     *  itself; nought is held where the run holds it. */
    @Test
    void theEndOnNoughtsSideIsTheOneTaken() {
        assertEquals(number("-3"), new NumericDomain.Bounds(at("-5", true), at("-2", false))
                .aValueNearestNought(Granularity.DISCRETE));
        assertEquals(number("-2.5"), new NumericDomain.Bounds(null, at("-2.5", true))
                .aValueNearestNought(Granularity.DENSE));
        assertEquals(ExactRatio.ZERO, new NumericDomain.Bounds(at("-1", false), null)
                .aValueNearestNought(Granularity.DENSE));
    }

    /** The end the other way, asked for itself: the greatest a run holds, or a step below an end
     *  it leaves out. */
    @Test
    void eitherEndIsAskedAlike() {
        NumericDomain.Bounds run = new NumericDomain.Bounds(at("1", true), at("31", false));
        assertEquals(number("30"), run.aValueNearestItsEnd(true, Granularity.DISCRETE));
        assertEquals(number("30"), run.aValueNearestItsEnd(true, Granularity.DENSE));
        assertEquals(number("1"), run.aValueNearestItsEnd(false, Granularity.DENSE));
        assertNull(new NumericDomain.Bounds(at("1", true), null)
                .aValueNearestItsEnd(true, Granularity.DISCRETE));
    }
}
