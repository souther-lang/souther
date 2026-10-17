package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.function.LongPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The whole numbers a statement about one number leaves are exactly the numbers it holds of.
 *
 * <p>Checked against the comparisons themselves, number by number, over a window wide enough to
 * hold every threshold below and some way past each: a run that went one too far or stopped one
 * short is a value a path would refuse or let through that the condition does the other way.
 */
class WholeNumbersLeftTest {

    private static final long WINDOW = 12;

    private static final List<ExactRatio> THRESHOLDS = List.of(ExactRatio.of(-3), ExactRatio.of(0),
            ExactRatio.of(4), ExactRatio.of(BigInteger.valueOf(5), BigInteger.TWO),
            ExactRatio.of(BigInteger.valueOf(-7), BigInteger.valueOf(3)));

    @Test
    void aComparisonLeavesTheNumbersItHoldsOf() {
        for (Rel rel : Rel.values()) {
            for (ExactRatio at : THRESHOLDS) {
                assertLeaves(WholeNumbersLeft.standing(rel, at), holding(rel, at), rel + " " + at);
            }
        }
    }

    @Test
    void bothAndEitherAndNeitherLeaveWhatTheyHoldOf() {
        for (Rel first : Rel.values()) {
            for (Rel second : Rel.values()) {
                for (ExactRatio one : THRESHOLDS) {
                    for (ExactRatio other : THRESHOLDS) {
                        WholeNumbersLeft a = WholeNumbersLeft.standing(first, one);
                        WholeNumbersLeft b = WholeNumbersLeft.standing(second, other);
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

    @Test
    void aSetWithEndsCountsAndListsWhatItHolds() {
        WholeNumbersLeft some = WholeNumbersLeft.one(BigInteger.ZERO, BigInteger.valueOf(3))
                .or(WholeNumbersLeft.one(BigInteger.valueOf(6), BigInteger.valueOf(6)));
        assertEquals(BigInteger.valueOf(5), some.count());
        assertEquals(List.of(0L, 1L, 2L, 3L, 6L),
                some.each().stream().map(BigInteger::longValueExact).toList());
        assertEquals(null, some.others().count(), "what it leaves out runs as far as numbers do");
        assertEquals(2, some.runs().size(), "three to six is a gap, and nought to three one run");
    }

    /** Whether a number stands {@code rel} to {@code at}, asked of the number itself. */
    private static LongPredicate holding(Rel rel, ExactRatio at) {
        return n -> rel.holds(ExactRatio.of(n).compareTo(at));
    }

    private static void assertLeaves(WholeNumbersLeft left, LongPredicate holds, String said) {
        List<Long> expected = new ArrayList<>();
        List<Long> actual = new ArrayList<>();
        for (long n = -WINDOW; n <= WINDOW; n++) {
            if (holds.test(n)) {
                expected.add(n);
            }
            if (contains(left, n)) {
                actual.add(n);
            }
        }
        assertEquals(expected, actual, said);
    }

    private static boolean contains(WholeNumbersLeft left, long n) {
        BigInteger at = BigInteger.valueOf(n);
        return left.runs().stream().anyMatch(run -> (run.from() == null
                || run.from().compareTo(at) <= 0) && (run.to() == null || run.to().compareTo(at) >= 0));
    }
}
