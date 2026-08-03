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
}
