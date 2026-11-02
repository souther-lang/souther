package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.UndividedByARelation.WholeEnds;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number moved by a weight and added to a rest brings the sum to every remainder by a divisor
 * where the values of it that keep the sum inside the Ints include as many side by side as there
 * are remainders, and that is least at one end of what the rest comes to or the other.
 */
class TheWindowThatKeepsAFormInsideTheIntsHoldsEveryRemainderTest {

    private static final BigInteger LEAST = BigInteger.valueOf(Long.MIN_VALUE);
    private static final BigInteger GREATEST = BigInteger.valueOf(Long.MAX_VALUE);
    private static final BigInteger SEVEN = BigInteger.valueOf(7);

    @Test
    void aRestInsideTheIntsLeavesTheWholeRunOfTheNumber() {
        assertTrue(holds(1, ends(-100, 100), -10, 10, SEVEN));
    }

    @Test
    void aRestPastTheGreatestIntAtItsHighEndLeavesTheNumberNoRoomThere() {
        assertFalse(holds(1, ends(-100, 100), -10, GREATEST.add(BigInteger.valueOf(200)), SEVEN));
    }

    @Test
    void aRestPastTheLeastIntAtItsLowEndLeavesTheNumberNoRoomThere() {
        assertFalse(holds(1, ends(-100, 100), LEAST.subtract(BigInteger.valueOf(200)), 10, SEVEN));
    }

    @Test
    void aWeightBelowNoughtTakesTheNumberTheOtherWayRound() {
        assertTrue(holds(-1, ends(-100, 100), -10, 10, SEVEN));
        assertFalse(holds(-1, ends(-100, 100), -10, GREATEST.add(BigInteger.valueOf(200)), SEVEN));
        assertFalse(holds(-1, ends(-100, 100), LEAST.subtract(BigInteger.valueOf(200)), 10, SEVEN));
    }

    @Test
    void theValuesOfTheNumberAreAsManyAsTheDivisorOrTheyAreNot() {
        assertTrue(holds(1, ends(0, 6), 0, 0, SEVEN));
        assertFalse(holds(1, ends(0, 5), 0, 0, SEVEN));
    }

    @Test
    void aNumberWithNoEndIsHeldOnlyByTheIntsThemselves() {
        assertTrue(holds(1, new WholeEnds(null, null), -10, 10, SEVEN));
        assertFalse(holds(1, new WholeEnds(null, null), 0, 0, GREATEST.shiftLeft(2)));
    }

    private static boolean holds(long weight, WholeEnds mine, long lowest, long highest,
                                 BigInteger divisor) {
        return holds(weight, mine, BigInteger.valueOf(lowest), BigInteger.valueOf(highest), divisor);
    }

    private static boolean holds(long weight, WholeEnds mine, long lowest, BigInteger highest,
                                 BigInteger divisor) {
        return holds(weight, mine, BigInteger.valueOf(lowest), highest, divisor);
    }

    private static boolean holds(long weight, WholeEnds mine, BigInteger lowest, long highest,
                                 BigInteger divisor) {
        return holds(weight, mine, lowest, BigInteger.valueOf(highest), divisor);
    }

    private static boolean holds(long weight, WholeEnds mine, BigInteger lowest,
                                 BigInteger highest, BigInteger divisor) {
        return UndividedByARelation.windowHoldsEveryRemainder(BigInteger.valueOf(weight), mine,
                lowest, highest, divisor, LEAST, GREATEST);
    }

    private static WholeEnds ends(long low, long high) {
        return new WholeEnds(BigInteger.valueOf(low), BigInteger.valueOf(high));
    }
}
