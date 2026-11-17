package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.WholeNumberRuns;

import java.math.BigInteger;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A date's year, moved by a whole number, leaves a remainder by a divisor where the year leaves what
 * the moved year does less the move: worked over the whole number, whatever it holds, and not over
 * its least bits.
 */
class TheYearsARemainderLeavesAreTheOnesOfTheYearTest {

    private static final List<BigInteger> MOVES = List.of(
            BigInteger.ZERO, BigInteger.ONE, BigInteger.valueOf(-1),
            BigInteger.TWO.pow(31), BigInteger.TWO.pow(31).negate(),
            BigInteger.TWO.pow(32), BigInteger.TWO.pow(32).negate(),
            BigInteger.TWO.pow(63).add(BigInteger.valueOf(5)),
            BigInteger.TWO.pow(100).negate());

    @Test
    void theYearsLeftAreTheYearsWhoseMovedYearLeavesOneOfTheRemaindersForEveryMove() {
        for (BigInteger moved : MOVES) {
            for (int divisor : new int[] {2, 7, 100, 399, 400}) {
                WholeNumberRuns leaves = WholeNumberRuns.of(List.of(BigInteger.ZERO));
                Set<Integer> years = WayToTheBorder.yearsLeaving(moved, divisor, leaves);
                for (int year = -divisor; year <= 2 * divisor; year++) {
                    BigInteger remainder = BigInteger.valueOf(year).add(moved)
                            .mod(BigInteger.valueOf(divisor));
                    assertEquals(leaves.holds(remainder),
                            years.contains(Math.floorMod(year, divisor)),
                            "year " + year + " moved by " + moved + " by " + divisor);
                }
            }
        }
    }
}
