package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Towards;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.ValueSet;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value inside a run of an order with no step is worked out from the ends, and a value beside one
 * singled out from it, and where this cannot hold the value it works out, it offers none.
 *
 * <p>None is what this already says for a value it composed nothing of, and never that the run is
 * empty. A run from a decimal of a scale near the end of the range to one holds every value between
 * them; halfway between is a number of more places than any number here can be held in.
 */
class AValueInsideARunWithNoStepIsWorkedOutOrNotOfferedTest {

    private static final Carrier DECIMALS = new Carrier.Dense();

    /** A tenth to the power of a scale near the end of the range. */
    private static final Count FINE = new Count(new BigDecimal(BigInteger.ONE, 1 << 30));

    /** Open at both ends, so the value is the one halfway, and from both ends asked. */
    @Test
    void halfwayBetweenAFineEndAndOneIsNotOffered() {
        for (Towards from : Towards.values()) {
            assertNull(DECIMALS.somethingInside(Endpoint.exclusive(FINE),
                            Endpoint.exclusive(Count.of(1)), from),
                    () -> "halfway is no number this holds, from " + from);
        }
    }

    /** Open at the fine end and unbounded at the other, so the value is one in from that end. */
    @Test
    void oneInFromAFineEndIsNotOffered() {
        assertNull(DECIMALS.somethingInside(Endpoint.exclusive(FINE), null, Towards.ABOVE),
                "one above a fine end is no number this holds");
    }

    /** And the same shapes over ends this can hold answer, which is the control. */
    @Test
    void theSameShapesOverOrdinaryEndsAreAnswered() {
        assertValue("0.5", DECIMALS.somethingInside(Endpoint.exclusive(Count.of(0)),
                Endpoint.exclusive(Count.of(1)), Towards.ABOVE));
        assertValue("0.5", DECIMALS.somethingInside(Endpoint.exclusive(Count.of(0)),
                Endpoint.exclusive(Count.of(1)), Towards.BELOW));
        assertValue("1", DECIMALS.somethingInside(Endpoint.exclusive(Count.of(0)), null,
                Towards.ABOVE));
        assertValue("-1", DECIMALS.somethingInside(null, Endpoint.exclusive(Count.of(0)),
                Towards.BELOW));
    }

    /**
     * A value other than a fine one, where nothing bounds the position: the place one away from
     * it is no number this holds, so it is not offered, and what is offered is none of the singled.
     */
    @Test
    void aPlaceOneAwayFromAFineValueIsNotOffered() {
        Place at = DECIMALS.somethingOtherThan(PlacesApart.of(List.of(FINE)), null, ValueSet.ANY,
                PatternPlan.Budget.OF_A_WITNESS.meter());

        assertTrue(at == null || !at.sameAs(FINE), () -> "the singled value was offered: " + at);
    }

    /** And one away from an ordinary value is what is offered first, which is the control. */
    @Test
    void aPlaceOneAwayFromAnOrdinaryValueIsOffered() {
        assertValue("1.5", DECIMALS.somethingOtherThan(
                PlacesApart.of(List.of(new Count(new BigDecimal("0.5")))), null, ValueSet.ANY,
                PatternPlan.Budget.OF_A_WITNESS.meter()));
    }

    private static void assertValue(String expected, Place at) {
        assertEquals(0, new BigDecimal(expected).compareTo(((Count) at).at()),
                () -> "expected " + expected + " and got " + at);
    }
}
