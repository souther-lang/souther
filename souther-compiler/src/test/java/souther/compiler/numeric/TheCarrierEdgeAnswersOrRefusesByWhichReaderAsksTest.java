package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The edge exact reasoning becomes a value on a carrier at, asked by its two kinds of reader.
 *
 * <p>Two readers and one edge. One is asking whether a count is this number — a line at a third is
 * no value of any position, and that is an answer about the model. The other has established that
 * one is: a level the written form attains is a whole multiple of what that form wrote, so reading
 * it back in the quantity's own units lands on a number the order has. A missing count means
 * opposite things to them, so which reader a caller is belongs in the signature
 * ({@link Count#at} against {@link Count#number(ExactRatio)}).
 *
 * <p><b>Said here rather than at each crossing.</b> Written as one door with a nullable answer,
 * every caller that had established there is a count had to invent what to do with an absence it
 * could mean nothing by — and one of them handed back a level of the exact side under a name saying
 * it was a value of a carrier, which travels until something far away asks that level for a place.
 */
class TheCarrierEdgeAnswersOrRefusesByWhichReaderAsksTest {

    private static ExactRatio ratio(long over, long under) {
        return ExactRatio.of(BigInteger.valueOf(over), BigInteger.valueOf(under));
    }

    /** A number some carrier's order counts to comes back from both, and is one count. */
    @Test
    void bothDoorsAnswerWithTheCountWhereOneIsTheNumber() {
        ExactRatio four = ExactRatio.of(4);

        assertEquals(new Count(new BigDecimal(4)), Count.at(four));
        assertEquals(Count.at(four), Count.number(four),
                "one edge, so the two readers are told the same thing where there is something"
                        + " to tell");
    }

    /**
     * And a number none counts to is an absence to one and a refusal to the other.
     *
     * <p>The whole of what the pair is for. Answered alike, one of the two readers is wrong: a
     * reader asking whether a position holds a value would be stopped by a third, and a reader that
     * has established it holds one would carry the absence somewhere it means nothing.
     */
    @Test
    void aNumberNoCarrierCountsToIsAnAbsenceToOneAndARefusalToTheOther() {
        ExactRatio aThird = ratio(1, 3);

        assertNull(Count.at(aThird), "no count is a third, which is an answer about the model");
        assertThrows(IllegalStateException.class, () -> Count.number(aThird),
                "and a reader holding one that has to be a count is holding this compiler's own"
                        + " mistake");
    }

    /**
     * What is refused is the number and never the carrier's grid.
     *
     * <p>A half is a count, and no whole-numbered order stands at one — which is the carrier's own
     * answer and asked of the carrier ({@link Granularity}). Folded in here, this edge would refuse
     * a number that is a count on some orders and the two questions would be one again.
     */
    @Test
    void aCountNoWholeNumberedOrderStandsAtIsStillACount() {
        ExactRatio aHalf = ratio(1, 2);

        assertEquals(new Count(new BigDecimal("0.5")), Count.at(aHalf));
        assertEquals(new Count(new BigDecimal("0.5")), Count.number(aHalf));
    }
}
