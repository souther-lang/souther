package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An end that is no decimal still has a least and a greatest decimal beside it, and the two are
 * told apart from where they lie and not from the end alone.
 */
class AnEndNoDecimalWritesIsMovedOntoTheGridNotGivenUpTest {

    private static final ExactRatio THIRD = ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3));

    private static final ExactRatio TWO_THIRDS = ExactRatio.of(BigInteger.TWO,
            BigInteger.valueOf(3));

    /** The run from a third to a third holds no decimal: the one above it is past the one below. */
    @Test
    void theLeastAboveAnEndIsPastTheGreatestBelowIt() {
        Lattice.Point least = Lattice.least(Granularity.DENSE, ExactCut.inclusive(THIRD));
        Lattice.Point greatest = Lattice.greatest(Granularity.DENSE, ExactCut.inclusive(THIRD));
        assertEquals(1, Lattice.compare(least, greatest));
        assertEquals(-1, Lattice.compare(greatest, least));
    }

    @Test
    void aRunFromAThirdToTwoThirdsHoldsAPoint() {
        Lattice.Point least = Lattice.least(Granularity.DENSE, ExactCut.exclusive(THIRD));
        Lattice.Point greatest = Lattice.greatest(Granularity.DENSE, ExactCut.exclusive(TWO_THIRDS));
        assertEquals(-1, Lattice.compare(least, greatest));
    }

    /** From nought, left out, to half a step: the step is the least and nought the greatest. */
    @Test
    void aRunUnderAStepHoldsNoPointWhateverItsEndsAre() {
        ExactRatio halfAStep = ExactRatio.of(BigInteger.ONE, BigInteger.TWO)
                .times(ExactRatio.of(new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE))).orNull();
        Lattice.Point least = Lattice.least(Granularity.DENSE, ExactCut.exclusive(ExactRatio.ZERO));
        Lattice.Point greatest = Lattice.greatest(Granularity.DENSE, ExactCut.inclusive(halfAStep));
        assertEquals(1, Lattice.compare(least, greatest));
    }

    /**
     * Two ends under the finest step, whose difference is no number that can be held: the run
     * between them holds no decimal, and nothing is told of their order by the ends alone.
     */
    @Test
    void anOrderOfEndsWhoseDifferenceIsNotHeldIsNotWorkedOut() {
        ExactRatio step = ExactRatio.of(new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE));
        ExactRatio squared = step.times(step).orNull();
        ExactRatio cubed = squared.times(step).orNull();
        Lattice.Point least = Lattice.least(Granularity.DENSE, ExactCut.inclusive(cubed));
        Lattice.Point greatest = Lattice.greatest(Granularity.DENSE, ExactCut.inclusive(squared));
        assertEquals(null, Lattice.compare(least, greatest));
    }

    /** A decimal and an end beside it are told apart by which side of the end the decimal lies. */
    @Test
    void aDecimalIsBelowTheLeastPointAboveAnEndJustAboveIt() {
        Lattice.Point decimal = Lattice.least(Granularity.DENSE,
                ExactCut.inclusive(ExactRatio.of(new BigDecimal("0.3333"))));
        Lattice.Point above = Lattice.least(Granularity.DENSE, ExactCut.inclusive(THIRD));
        assertEquals(-1, Lattice.compare(decimal, above));
        assertEquals(1, Lattice.compare(above, decimal));
    }
}
