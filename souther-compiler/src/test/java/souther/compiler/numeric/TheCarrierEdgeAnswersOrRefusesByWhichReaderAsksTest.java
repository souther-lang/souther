package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * The edge exact reasoning becomes a value on a carrier at, and the three answers it has.
 *
 * <p>A number is a count, no count is it, or the host has no room to write the digits of the count
 * that is. The first two are facts about the number — a line at a third is no value of any position,
 * and that is an answer about the model. The third is a fact about the run and says nothing about
 * which values the order has, so it is neither of the first two: a reader that took it for the
 * second would say that no value exists where a machine ran out of room.
 *
 * <p><b>Said in the type rather than at each crossing.</b> Written as one door with a nullable
 * answer and an exception for the rest, every caller had to remember which of the three it might be
 * handed and what to do with the one it could mean nothing by.
 */
class TheCarrierEdgeAnswersOrRefusesByWhichReaderAsksTest {

    private static ExactRatio ratio(long over, long under) {
        return ExactRatio.of(BigInteger.valueOf(over), BigInteger.valueOf(under));
    }

    @Test
    void aNumberSomeCarriersOrderCountsToIsThatCount() {
        assertEquals(ExactAnswer.held(Optional.of(new Count(new BigDecimal(4)))),
                Count.written(ExactRatio.of(4)));
    }

    /** No count is a third, which is an answer about the model and not about the run. */
    @Test
    void aNumberNoCarrierCountsToIsAnAbsenceThatSaysSo() {
        assertEquals(ExactAnswer.held(Optional.empty()), Count.written(ratio(1, 3)));
    }

    /**
     * What is asked is the number and never the carrier's grid.
     *
     * <p>A half is a count, and no whole-numbered order stands at one — which is the carrier's own
     * answer and asked of the carrier ({@link Granularity}). Folded in here, this edge would refuse
     * a number that is a count on some orders and the two questions would be one again.
     */
    @Test
    void aCountNoWholeNumberedOrderStandsAtIsStillACount() {
        assertEquals(ExactAnswer.held(Optional.of(new Count(new BigDecimal("0.5")))),
                Count.written(ratio(1, 2)));
    }

    /**
     * A whole number with more digits than the host builds is a count, and the host cannot write it.
     *
     * <p>Two to the two-to-the-fortieth is a number a decimal holds at scale nought, so it is not the
     * absence above; and no host has room for its digits, so it is not a count either. It is
     * neither answer about the number, and is said as the third.
     */
    @Test
    void aNumberWhoseDigitsTheHostHasNoRoomForIsNeitherOfTheOtherTwo() {
        ExactRatio huge = new ExactRatio(BigInteger.ONE, BigInteger.ONE, 1L << 40, 0);

        assertFalse(Count.written(huge).isHeld());
        assertFalse(huge.writtenDecimal().isHeld());
    }
}
