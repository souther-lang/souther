package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.observe.ObservedValue;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.partition.QuantityFixtures.stands;

/**
 * Where a row stands at a remainder of a form is where the numbers it holds put the form, and not a
 * second account of how the run computed it.
 *
 * <p>A form keeps what an expression comes to and not the order its steps were taken in. {@code a - d}
 * at {@code -1} and the least {@code Int} is held as {@code a + (-1)·d}, whose product is out of
 * range, and it is a difference that is not: the subtraction runs and comes to the greatest
 * {@code Int}. Read step by step off the form, the row would be one nothing could be told about
 * although the program ran it. Whether the program ran is what the run says, and a row is certified
 * from that.
 */
class ARemainderOfAFormStandsWhereTheNumbersTheRowHoldsPutItTest {

    private static final TermPath A = TermPath.of("a");

    private static final TermPath D = TermPath.of("d");

    /** {@code Int.floorMod(a - d, 7)}. */
    private static final BorderQuantity.RemainderOfAForm REMAINDER = remainderOfADifference();

    private static final long LEAST = Long.MIN_VALUE;

    @Test
    void aDifferenceTheRunComputesStandsWhereItsRemainderPutsIt() {
        // -1 - least comes to the greatest Int, which leaves nought by seven.
        assertEquals(BorderQuantity.Stands.YES,
                stands(REMAINDER, remainder(0), row(-1, LEAST)),
                "the subtraction runs, and the greatest Int is a multiple of seven");
        assertEquals(BorderQuantity.Stands.NO,
                stands(REMAINDER, remainder(1), row(-1, LEAST)),
                "and it leaves nothing else");
    }

    @Test
    void aSmallDifferenceStandsWhereItsRemainderPutsIt() {
        assertEquals(BorderQuantity.Stands.YES, stands(REMAINDER, remainder(3), row(10, 0)));
        assertEquals(BorderQuantity.Stands.YES, stands(REMAINDER, remainder(4), row(0, 10)));
    }

    private static Criterion remainder(long at) {
        return new Criterion.AtTheLevel(Level.OfTheQuantity.of(at));
    }

    private static BorderQuantity.RemainderOfAForm remainderOfADifference() {
        NumericTerm a = new NumericTerm.ValueOf(A);
        NumericTerm d = new NumericTerm.ValueOf(D);
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(a, ExactRatio.ONE);
        coefs.put(d, ExactRatio.ONE.negated());
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(a, TermOrdersFixtures.itself(a, Carrier.WHOLE));
        on.put(d, TermOrdersFixtures.itself(d, Carrier.WHOLE));
        return new BorderQuantity.RemainderOfAForm("decide",
                new BorderQuantity.OverAForm("decide",
                        new LinearForm<>(ExactRatio.ZERO, coefs), on),
                BigInteger.ZERO, BigInteger.valueOf(7));
    }

    private static BorderQuantity.Observation row(long a, long d) {
        return new AnObservationOfAForm() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                return WalkResult.reached(new ObservationAtPoint.Value(
                        new ObservedValue.Integer(A.equals(path) ? a : d)));
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a number of one position is not read over a run");
            }
        };
    }
}
