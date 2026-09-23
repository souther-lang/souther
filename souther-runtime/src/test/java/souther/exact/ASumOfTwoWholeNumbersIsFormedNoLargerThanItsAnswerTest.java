package souther.exact;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A sum of two odd numbers is formed no larger than the greater of them.
 *
 * <p>Which is the sum that wants a bit neither side can give back, and the one the host's largest whole
 * number therefore turns away while the value it stands for is ordinary: three below a power of two and
 * three above it add to that power, whose place is one numerator and one exponent. So where both are odd
 * the odd part of the sum is formed and the factor of two goes to the exponent.
 *
 * <p>Not a law about sums in general — fifteen and eight make a longer number than either, and this takes
 * nothing off that. The bound is on what is stored, and what is stored holds no factor of two; a sum with
 * one side odd is odd and is already the size its numerator will be.
 *
 * <p>Stated over sizes a test can hold, because the bit past the host's own end needs a pair of numbers of
 * hundreds of megabytes to reach — and it is this property, not that pair, that decides whether reaching it
 * fails.
 */
class ASumOfTwoWholeNumbersIsFormedNoLargerThanItsAnswerTest {

    @Test
    void aSumOfTwoOddNumbersIsFormedNoLargerThanEither() {
        for (int bits : new int[] {8, 41, 200}) {
            BigInteger power = BigInteger.TWO.pow(bits);
            for (BigInteger apart : List.of(BigInteger.ONE, BigInteger.valueOf(3),
                    BigInteger.valueOf(1023))) {
                BigInteger below = power.subtract(apart);
                BigInteger above = power.add(apart);
                for (int sign : new int[] {1, -1}) {
                    BigInteger a = below.multiply(BigInteger.valueOf(sign));
                    BigInteger b = above.multiply(BigInteger.valueOf(sign));
                    ExactArithmetic.Summed sum = ExactArithmetic.summed(a, b);

                    assertEquals(a.add(b), sum.whole().shiftLeft(sum.twos()),
                            "the sum is the value it stands for: " + a + " and " + b);
                    assertTrue(sum.whole().abs().bitLength()
                                    <= Math.max(a.abs().bitLength(), b.abs().bitLength()),
                            "and is no larger than either: " + sum.whole().abs().bitLength());
                }
            }
        }
    }

    /** And a sum of numbers a factor of two runs through is formed with that factor taken off, however
     *  many of them there are — the same property, reached by both sides having a bit to give back. */
    @Test
    void aSumOfTwoEvenNumbersComesDownBeforeItIsFormed() {
        BigInteger power = BigInteger.TWO.pow(60);
        ExactArithmetic.Summed sum = ExactArithmetic.summed(
                power.subtract(BigInteger.valueOf(8)), power.add(BigInteger.valueOf(8)));

        assertEquals(BigInteger.TWO.pow(57), sum.whole());
        assertEquals(4, sum.twos(), "three from both sides being even, and one from both being odd");
    }
}
