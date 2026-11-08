package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.LongPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The whole numbers a statement about one number leaves are exactly the numbers it holds of.
 *
 * <p>Checked against the comparisons themselves, number by number, over a window wide enough to
 * hold every threshold below and some way past each: a run that went one too far or stopped one
 * short is a value a path would refuse or let through that the condition does the other way.
 */
class WholeNumberRunsTest {

    private static final long WINDOW = 12;

    private static final List<ExactRatio> THRESHOLDS = List.of(ExactRatio.of(-3), ExactRatio.of(0),
            ExactRatio.of(4), ExactRatio.of(BigInteger.valueOf(5), BigInteger.TWO),
            ExactRatio.of(BigInteger.valueOf(-7), BigInteger.valueOf(3)));

    @Test
    void aComparisonLeavesTheNumbersItHoldsOf() {
        for (Rel rel : Rel.values()) {
            for (ExactRatio at : THRESHOLDS) {
                assertLeaves(WholeNumberRuns.standing(rel, at), holding(rel, at), rel + " " + at);
            }
        }
    }

    @Test
    void bothAndEitherAndNeitherLeaveWhatTheyHoldOf() {
        for (Rel first : Rel.values()) {
            for (Rel second : Rel.values()) {
                for (ExactRatio one : THRESHOLDS) {
                    for (ExactRatio other : THRESHOLDS) {
                        WholeNumberRuns a = WholeNumberRuns.standing(first, one);
                        WholeNumberRuns b = WholeNumberRuns.standing(second, other);
                        LongPredicate p = holding(first, one);
                        LongPredicate q = holding(second, other);
                        String said = first + " " + one + ", " + second + " " + other;
                        assertLeaves(a.and(b), p.and(q), "both " + said);
                        assertLeaves(a.or(b), p.or(q), "either " + said);
                        assertLeaves(a.or(b).others(), p.or(q).negate(), "neither " + said);
                    }
                }
            }
        }
    }

    /** A thousand million numbers and one more are two runs, and counted off their ends. */
    @Test
    void aRunIsHeldByItsEndsHoweverManyNumbersItHolds() {
        BigInteger most = BigInteger.valueOf(999_999_999);
        WholeNumberRuns some = WholeNumberRuns.one(BigInteger.ZERO, BigInteger.valueOf(498))
                .or(WholeNumberRuns.one(most, most));
        assertEquals(2, some.runs().size());
        assertEquals(BigInteger.valueOf(500), some.count());
        assertEquals(List.of(new WholeNumberRuns.Run(BigInteger.valueOf(499),
                        most.subtract(BigInteger.ONE))),
                some.others().and(WholeNumberRuns.one(BigInteger.ZERO, most)).runs());
        assertNull(some.others().count(), "what it leaves out runs as far as numbers do");
        assertTrue(WholeNumberRuns.of(List.of(BigInteger.ONE, BigInteger.valueOf(3)))
                .isNumbersApart());
    }

    /** The whole numbers between two ends, held or not, at a count that may be no whole number. */
    @Test
    void theWholeNumbersBetweenTwoEndsAreTheOnesInside() {
        Endpoint low = Endpoint.exclusive(new Count(new BigDecimal("1.5")));
        Endpoint high = Endpoint.inclusive(new Count(new BigDecimal("4")));
        assertEquals(WholeNumberRuns.one(BigInteger.TWO, BigInteger.valueOf(4)),
                WholeNumberRuns.between(low, high));
        assertEquals(WholeNumberRuns.one(BigInteger.TWO, BigInteger.valueOf(3)),
                WholeNumberRuns.between(low, Endpoint.exclusive(new Count(new BigDecimal("4")))));
        assertEquals(WholeNumberRuns.EVERY, WholeNumberRuns.between(null, null));
        assertEquals(WholeNumberRuns.NONE, WholeNumberRuns.between(high, low));
    }

    /** Whether a number stands {@code rel} to {@code at}, asked of the number itself. */
    private static LongPredicate holding(Rel rel, ExactRatio at) {
        return n -> rel.holds(ExactRatio.of(n).compareTo(at));
    }

    private static void assertLeaves(WholeNumberRuns left, LongPredicate holds, String said) {
        List<Long> expected = new ArrayList<>();
        List<Long> actual = new ArrayList<>();
        for (long n = -WINDOW; n <= WINDOW; n++) {
            if (holds.test(n)) {
                expected.add(n);
            }
            if (left.holds(BigInteger.valueOf(n))) {
                actual.add(n);
            }
        }
        assertEquals(expected, actual, said);
    }
}
