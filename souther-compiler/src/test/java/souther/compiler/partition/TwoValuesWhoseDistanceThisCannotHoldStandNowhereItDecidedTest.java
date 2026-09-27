package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.partition.QuantityFixtures.stands;

/**
 * Two values a row wrote whose distance this compiler cannot hold stand at a place it could not
 * tell, and neither at the item nor away from it.
 *
 * <p>The values are both there and are both decimals the language has. What is out of reach is the
 * number one minus the other is: a decimal of a scale near the end of the range, taken from one,
 * has more places than any number here can be held in. Answered as not standing, the row would be
 * reported as missing the point; answered as standing, as covering it. Either is a claim about the
 * row that nothing here found out.
 */
class TwoValuesWhoseDistanceThisCannotHoldStandNowhereItDecidedTest {

    private static final TermPath ON = TermPath.of("on");

    private static final TermPath AGAINST = TermPath.of("against");

    private static final BorderQuantity.Apart PAIR = new BorderQuantity.Apart("decide",
            TermOrdersFixtures.itself(new NumericTerm.ValueOf(ON), new Carrier.Dense()),
            TermOrdersFixtures.itself(new NumericTerm.ValueOf(AGAINST), new Carrier.Dense()));

    /** Where the two meet, which is what {@code on == against} asks. */
    private static final Criterion WHERE_THEY_MEET = new Criterion.AtTheLevel(Level.WHERE_THEY_MEET);

    /** A tenth to the power of a scale near the end of the range. */
    private static final BigDecimal FINE = new BigDecimal(BigInteger.ONE, 1 << 30);

    @Test
    void aDistanceThisCannotHoldIsOneItCouldNotTellAbout() {
        assertEquals(BorderQuantity.Stands.couldNotTell(ReadingGap.COULD_NOT_WORK_OUT),
                stands(PAIR, WHERE_THEY_MEET, row(FINE, BigDecimal.ONE)),
                "the values are both there and what they come to was not worked out");
    }

    /**
     * And values a distance this can hold apart say where they stand, which is the control:
     * without it the answer above passes for a pair that can tell nothing at all.
     */
    @Test
    void aDistanceThisCanHoldIsAnswered() {
        assertEquals(BorderQuantity.Stands.YES,
                stands(PAIR, WHERE_THEY_MEET, row(new BigDecimal("0.10"), new BigDecimal("0.1"))),
                "a tenth meets a tenth however many places it is written to");
        assertEquals(BorderQuantity.Stands.NO,
                stands(PAIR, WHERE_THEY_MEET, row(new BigDecimal("0.1"), BigDecimal.ONE)),
                "and a tenth does not meet one");
    }

    private static BorderQuantity.Observation row(BigDecimal on, BigDecimal against) {
        return new BorderQuantity.Observation() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                return WalkResult.reached(new ObservationAtPoint.Value(
                        new ObservedValue.Decimal(ON.equals(path) ? on : against)));
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a number of one position is not read over a run");
            }
        };
    }
}
