package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.exact.ExactDecimals;
import souther.exact.ExactFailure;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

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
    void aProductHeldAtAnotherScaleIsStillACount() {
        // BigDecimal.multiply asks for the sum of the scales and refuses; the number is one of the
        // type's own, 10^-(2^31 - 1), at a scale one less than the sum.
        Count a = new Count(new BigDecimal(BigInteger.TEN, Integer.MAX_VALUE));
        BigDecimal b = new BigDecimal(BigInteger.ONE, 1);

        Count product = a.timesWhereHeld(b);

        assertNotNull(product);
        assertEquals(0, product.compareTo(FAR_FROM_NOUGHT));
    }

    @Test
    void aProductThatCarriesTheZerosTheScaleSumAsksForIsHeld() {
        // 2 * 5 is 10, so the digits give up the zero the scale sum is one over the range by.
        Count a = new Count(new BigDecimal(BigInteger.TWO, Integer.MAX_VALUE));
        BigDecimal b = new BigDecimal(BigInteger.valueOf(5), 1);

        Count product = a.timesWhereHeld(b);

        assertNotNull(product);
        assertEquals(0, product.compareTo(FAR_FROM_NOUGHT));
    }

    @Test
    void aProductBelowTheFloorOfTheScaleRangeIsHeldWithTheZerosItIsShortBy() {
        Count a = new Count(new BigDecimal(BigInteger.ONE, Integer.MIN_VALUE));

        Count product = a.timesWhereHeld(new BigDecimal(BigInteger.ONE, -1));

        assertNotNull(product);
        assertEquals(0, product.compareTo(
                new Count(new BigDecimal(BigInteger.TEN, Integer.MIN_VALUE))));
    }

    @Test
    void noDecimalIsANumberWhoseDigitsHaveNoZerosToBringItBackIntoTheRange() {
        assertNull(ExactDecimals.product(
                new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE), new BigDecimal(BigInteger.ONE, 1)));
    }

    @Test
    void aHostWithNoRoomForTheZerosIsAFailureAndNotAnAnswerAboutTheNumber() {
        BigDecimal floor = new BigDecimal(BigInteger.ONE, Integer.MIN_VALUE);

        assertThrows(ExactFailure.class, () -> ExactDecimals.product(floor, floor));
        assertNull(new Count(floor).timesWhereHeld(floor),
                "a reader that claims less reads both refusals as no count");
    }

    @Test
    void aCountAtTheFloorOfTheScaleRangeIsNamedByItsNumber() {
        Count tens = new Count(new BigDecimal(BigInteger.TEN, Integer.MIN_VALUE));
        Count hundreds = new Count(new BigDecimal(BigInteger.valueOf(100), Integer.MIN_VALUE + 1));

        assertEquals(tens.key(), hundreds.key());
        assertEquals(tens.canonical().at().scale(), hundreds.canonical().at().scale());
        assertTrue(tens.whole());
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
