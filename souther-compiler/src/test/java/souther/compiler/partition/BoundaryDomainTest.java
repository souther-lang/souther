package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.ObservedValue;

import java.math.BigDecimal;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Asking for the value beside a boundary is asking the type.
 *
 * <p>{@code cost <= 100000} wants 100001 tried as well, and that value exists because the type counts
 * in whole numbers. A decimal has no next value, and inventing one — 100000.01, or whatever scale
 * happens to be in the compiler — would test a rule the model never stated.
 */
class BoundaryDomainTest {

    @Test
    void aWholeNumberHasBothNeighbours() {
        ObservedValue hundred = new ObservedValue.Integer(100);

        assertEquals(Optional.of(new ObservedValue.Integer(101)),
                BoundaryDomain.INT.successor(hundred));
        assertEquals(Optional.of(new ObservedValue.Integer(99)),
                BoundaryDomain.INT.predecessor(hundred));
    }

    @Test
    void aWholeNumberAtTheEdgeOfItsRangeHasNoneOnThatSide() {
        assertTrue(BoundaryDomain.INT.successor(new ObservedValue.Integer(Long.MAX_VALUE)).isEmpty());
        assertTrue(BoundaryDomain.INT.predecessor(new ObservedValue.Integer(Long.MIN_VALUE)).isEmpty());
    }

    /** The restraint that matters: no epsilon is invented. */
    @Test
    void aDecimalHasNoNeighbourToGive() {
        ObservedValue amount = new ObservedValue.Decimal(new BigDecimal("100000"));

        assertTrue(BoundaryDomain.DECIMAL.successor(amount).isEmpty());
        assertTrue(BoundaryDomain.DECIMAL.predecessor(amount).isEmpty());
    }

    @Test
    void aMidpointIsAnOrdinaryValueOfEitherType() {
        assertEquals(Optional.of(new ObservedValue.Integer(50)),
                BoundaryDomain.INT.midpoint(new ObservedValue.Integer(0),
                        new ObservedValue.Integer(100)));
        assertEquals(Optional.of(new ObservedValue.Decimal(new BigDecimal("50"))),
                BoundaryDomain.DECIMAL.midpoint(new ObservedValue.Decimal(BigDecimal.ZERO),
                        new ObservedValue.Decimal(new BigDecimal("100"))));
    }

    @Test
    void aTypeThatCannotAnswerSaysSoRatherThanGuessing() {
        ObservedValue text = new ObservedValue.Text("x");

        assertTrue(BoundaryDomain.INT.successor(text).isEmpty());
        assertTrue(BoundaryDomain.NONE.successor(new ObservedValue.Integer(1)).isEmpty());
        assertTrue(BoundaryDomain.NONE.midpoint(new ObservedValue.Integer(0),
                new ObservedValue.Integer(2)).isEmpty());
    }

    /**
     * A date's neighbours and midpoint are dates, and the count carrying them stays whole.
     *
     * <p>Two days apart by one have a midpoint, and it is one of them: the carrier is a number of
     * days and there is no half a day in it. Taken over a carrier wider than the type — a decimal
     * halfway between two counts — the answer is not a date at all, and the value it would be
     * written from is one no calendar has.
     */
    @Test
    void aDateStepsAndMeetsInWholeDays() {
        ObservedValue first = new ObservedValue.Temporal("2026-01-01");
        ObservedValue second = new ObservedValue.Temporal("2026-01-02");

        assertEquals(Optional.of(second), BoundaryDomain.DATE.successor(first));
        assertEquals(Optional.of(first), BoundaryDomain.DATE.predecessor(second));
        assertEquals(Optional.of(first), BoundaryDomain.DATE.midpoint(first, second),
                "an odd number of days apart still meets at a day");
        assertEquals(Optional.of(second),
                BoundaryDomain.DATE.midpoint(first, new ObservedValue.Temporal("2026-01-03")));
    }
}
