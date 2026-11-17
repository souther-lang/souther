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

    /** Moves whose least 32 bits are another remainder by seven than the whole number is: 2^31 is 2
     *  and its least 32 bits are -2^31, which is 5; 2^32 is 4 and its least bits 0; and the same
     *  the other way. A move of nought is the control. */
    private static final List<BigInteger> MOVES = List.of(
            BigInteger.ZERO, BigInteger.TWO.pow(31), BigInteger.TWO.pow(32),
            BigInteger.TWO.pow(32).negate());

    @Test
    void theYearsLeftAreTheYearsWhoseMovedYearLeavesOneOfTheRemaindersForEveryMove() {
        int divisor = 7;
        WholeNumberRuns leaves = WholeNumberRuns.of(List.of(BigInteger.ZERO));
        for (BigInteger moved : MOVES) {
            Set<Integer> years = WayToTheBorder.yearsLeaving(moved, divisor, leaves);
            for (int year = 0; year < divisor; year++) {
                BigInteger remainder = BigInteger.valueOf(year).add(moved)
                        .mod(BigInteger.valueOf(divisor));
                assertEquals(leaves.holds(remainder), years.contains(year),
                        "year " + year + " moved by " + moved + " by " + divisor);
            }
        }
    }
}
