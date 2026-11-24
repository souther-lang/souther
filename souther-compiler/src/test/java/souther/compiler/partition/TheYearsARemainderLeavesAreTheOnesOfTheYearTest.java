package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
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

    /** Runs with an end open, below nought, past the divisor, apart from each other and of no
     *  number: each held to the remainders the run holds, one by one. */
    @Test
    void theYearsLeftAreTheSameWhateverTheEndsOfTheRunsAre() {
        int divisor = 7;
        List<WholeNumberRuns> all = List.of(
                WholeNumberRuns.EVERY, WholeNumberRuns.NONE,
                WholeNumberRuns.one(BigInteger.valueOf(-5), BigInteger.valueOf(2)),
                WholeNumberRuns.one(BigInteger.valueOf(5), BigInteger.valueOf(40)),
                WholeNumberRuns.one(BigInteger.valueOf(7), BigInteger.valueOf(9)),
                WholeNumberRuns.one(BigInteger.valueOf(-9), BigInteger.valueOf(-1)),
                WholeNumberRuns.one(BigInteger.valueOf(3), BigInteger.valueOf(3)),
                WholeNumberRuns.of(List.of(BigInteger.ONE, BigInteger.valueOf(6))),
                WholeNumberRuns.standing(Rel.GE, ExactRatio.of(4)),
                WholeNumberRuns.standing(Rel.LE, ExactRatio.of(2)));
        for (WholeNumberRuns leaves : all) {
            for (BigInteger moved : MOVES) {
                Set<Integer> years = WayToTheBorder.yearsLeaving(moved, divisor, leaves);
                for (int year = 0; year < divisor; year++) {
                    BigInteger remainder = BigInteger.valueOf(year).add(moved)
                            .mod(BigInteger.valueOf(divisor));
                    assertEquals(leaves.holds(remainder), years.contains(year),
                            leaves + " year " + year + " moved by " + moved);
                }
            }
        }
    }
}
