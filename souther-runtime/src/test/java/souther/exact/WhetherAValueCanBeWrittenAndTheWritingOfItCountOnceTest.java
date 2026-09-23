package souther.exact;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The question of whether a value can be written and the writing of it are answered by one count.
 *
 * <p>Two counts of the same budget are how a question and the building that answers it come apart, so a
 * caller deciding from the first would be refused by the second. Asked at the edge from the side that is
 * cheap to build: what the question refuses the writing refuses, and what it allows, at sizes a test
 * holds, the writing builds.
 */
class WhetherAValueCanBeWrittenAndTheWritingOfItCountOnceTest {

    private static final BigInteger PAST_WHAT_THE_HOST_ADDRESSES = BigInteger.valueOf(Integer.MAX_VALUE).add(BigInteger.ONE);

    @Test
    void whatTheQuestionRefusesTheWritingRefuses() {
        BigInteger[][] refused = {
                {BigInteger.ONE, PAST_WHAT_THE_HOST_ADDRESSES, BigInteger.ZERO},
                {BigInteger.ONE, BigInteger.ZERO, PAST_WHAT_THE_HOST_ADDRESSES},
                {BigInteger.ONE, BigInteger.ZERO, BigInteger.ONE.shiftLeft(30).add(BigInteger.ONE)},
                {BigInteger.ONE, BigInteger.ONE.shiftLeft(64), BigInteger.ZERO}};
        for (BigInteger[] each : refused) {
            assertFalse(ExactArithmetic.canBeWritten(each[0], each[1], each[2]));
            assertThrows(ExactRangeExceeded.class,
                    () -> ExactArithmetic.written(each[0], each[1], each[2]));
        }
    }

    @Test
    void whatTheQuestionAllowsTheWritingBuilds() {
        BigInteger whole = BigInteger.valueOf(3);
        assertTrue(ExactArithmetic.canBeWritten(whole, BigInteger.valueOf(4), BigInteger.valueOf(2)));
        assertEquals(BigInteger.valueOf(3 * 16 * 25),
                ExactArithmetic.written(whole, BigInteger.valueOf(4), BigInteger.valueOf(2)));
    }

    /** A value with no powers to write is the number it was handed, and is not copied to say so. */
    @Test
    void aValueWithNoPowersIsNotCopied() {
        BigInteger wide = BigInteger.ONE.shiftLeft(4000).subtract(BigInteger.valueOf(3));

        assertSame(wide, ExactArithmetic.written(wide, BigInteger.ZERO, BigInteger.ZERO));
    }
}
