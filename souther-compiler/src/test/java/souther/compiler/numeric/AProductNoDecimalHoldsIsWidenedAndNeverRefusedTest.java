package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A product of two counts is a number whether or not a {@code BigDecimal} holds it, and the analysis
 * that reads it takes the answer that claims least when none does.
 */
class AProductNoDecimalHoldsIsWidenedAndNeverRefusedTest {

    /** {@code 10^-(2^30)}: nonzero, and the least scale whose square leaves the range. */
    private static final Count TINY = new Count(new BigDecimal(BigInteger.ONE, 1 << 30));

    private static final Count FAR_FROM_NOUGHT = new Count(new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE));

    private static final BigDecimal WRITTEN_NOUGHT = new BigDecimal("0.0");

    @Test
    void aProductWhoseScaleLeavesTheRangeIsNoCount() {
        assertNull(TINY.timesWhereHeld(TINY.at()));
    }

    @Test
    void nothingTimesAnythingIsNoughtAtAnyScale() {
        assertEquals(0, FAR_FROM_NOUGHT.timesWhereHeld(WRITTEN_NOUGHT).compareTo(Count.ZERO));
        assertEquals(0, Count.ZERO.timesWhereHeld(FAR_FROM_NOUGHT.at()).compareTo(Count.ZERO));
    }

    @Test
    void aCornerAtNoughtIsNoughtWhateverTheOtherFactorsScaleIs() {
        NumericDomain.Bounds fromNought = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.ZERO), Endpoint.inclusive(TINY));
        NumericDomain.Bounds tiny = new NumericDomain.Bounds(
                Endpoint.inclusive(TINY), Endpoint.inclusive(TINY));

        NumericDomain.Bounds product = Intervals.product(fromNought, tiny);

        assertEquals(0, ((Count) product.min().at()).compareTo(Count.ZERO));
        assertEquals(true, product.min().inclusive(), "the product takes nought where a factor does");
        assertNull(product.max(), "the far corner is a positive number of no size");
    }

    @Test
    void anEndTheProductHasNoCountForBoundsNothingItsSignPointsTo() {
        NumericDomain.Bounds tiny = new NumericDomain.Bounds(
                Endpoint.inclusive(TINY), Endpoint.inclusive(Count.of(5)));

        NumericDomain.Bounds product = Intervals.product(tiny, tiny);

        assertNotNull(product.min(), "the product does not cross zero");
        assertEquals(0, ((Count) product.min().at()).compareTo(Count.ZERO),
                "and it is no nearer to it than zero: its least corner is a number of no size");
        assertNull(product.max(), "a positive number of no size may be beyond every bound");
    }

    @Test
    void aNegativeNumberOfNoSizeIsBoundedAboveByNoughtAndByNothingBelow() {
        NumericDomain.Bounds below = new NumericDomain.Bounds(
                Endpoint.inclusive(TINY.negate()), Endpoint.inclusive(TINY.negate()));
        NumericDomain.Bounds above = new NumericDomain.Bounds(
                Endpoint.inclusive(TINY), Endpoint.inclusive(TINY));

        NumericDomain.Bounds product = Intervals.product(below, above);

        assertNull(product.min());
        assertEquals(0, ((Count) product.max().at()).compareTo(Count.ZERO));
    }
}
