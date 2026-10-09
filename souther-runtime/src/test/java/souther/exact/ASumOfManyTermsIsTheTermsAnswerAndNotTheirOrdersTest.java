package souther.exact;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The exact sum of many terms is one answer for the terms, in whatever order they come, and is
 * refused only where the sum itself is.
 *
 * <p>A run of two-term sums asks every partial sum to be held. A partial sum can fail where the
 * whole does not, in two ways: two terms at the greatest exponent add to one whose exponent is past
 * the range, and a fine term and an ordinary one have a sum with as many digits as their exponents
 * are apart. In both, terms after them can cancel what failed, and the run would have ended or not
 * by the order the terms came in.
 */
class ASumOfManyTermsIsTheTermsAnswerAndNotTheirOrdersTest {

    private static final ExactParts ONE = new ExactParts(BigInteger.ONE, BigInteger.ONE, 0, 0);

    /** One at the greatest power of two. */
    private static final ExactParts GREATEST =
            new ExactParts(BigInteger.ONE, BigInteger.ONE, Long.MAX_VALUE, 0);

    /** A tenth to the power of a scale near the end of the range. */
    private static final ExactParts FINE =
            new ExactParts(BigInteger.ONE, BigInteger.ONE, -(1L << 30), -(1L << 30));

    @Test
    void termsAtTheGreatestExponentThatCancelAreNought() {
        assertThrows(ExactRangeExceeded.class, () -> ExactArithmetic.plus(GREATEST, GREATEST),
                "two of them alone add past the range");
        for (List<ExactParts> order : orders(List.of(GREATEST, GREATEST, negated(GREATEST),
                negated(GREATEST)))) {
            assertEquals(ExactParts.ZERO, ExactArithmetic.sum(order), () -> "in the order " + order);
        }
    }

    @Test
    void aFineTermAndItsNegationCancelWhereverAnOrdinaryOneStands() {
        for (List<ExactParts> order : orders(List.of(FINE, ONE, negated(FINE)))) {
            assertEquals(ONE, ExactArithmetic.sum(order), () -> "in the order " + order);
        }
    }

    /**
     * Terms that cancel across two scales meet before either is aligned with a third that stands
     * between them in the order of scales: the two nearest in scale meet first, not the two that
     * come first.
     *
     * <p>Two fine terms make twice one at their scale, and twice one at the scale a power of two
     * above cancels it; a term fine in its twos alone stands between them in the order of scales,
     * and met with either first has a sum with as many digits as their fives are apart.
     */
    @Test
    void theNearestInScaleMeetFirstAndNotTheFirstInTheOrderOfScales() {
        long n = 1L << 30;
        ExactParts twiceNegated = new ExactParts(BigInteger.ONE.negate(), BigInteger.ONE, -n + 1,
                -n);
        ExactParts fineInTwos = new ExactParts(BigInteger.ONE, BigInteger.ONE, -n, 0);
        for (List<ExactParts> order : orders(List.of(fineInTwos, FINE, FINE, twiceNegated))) {
            assertEquals(fineInTwos, ExactArithmetic.sum(order), () -> "in the order " + order);
        }
    }

    @Test
    void aSumPastTheRangeIsRefusedWhateverTheOrder() {
        for (List<ExactParts> order : orders(List.of(GREATEST, GREATEST))) {
            assertThrows(ExactRangeExceeded.class, () -> ExactArithmetic.sum(order),
                    () -> "in the order " + order);
        }
    }

    /** And every meeting is told, so a caller paying for the work pays for each. */
    @Test
    void everyMeetingIsToldBeforeItIsMade() {
        List<String> met = new ArrayList<>();
        ExactArithmetic.sum(List.of(ONE, ONE, ONE), (one, other) -> met.add(one + "+" + other));
        assertEquals(2, met.size(), () -> "two meetings make one sum of three: " + met);
    }

    private static ExactParts negated(ExactParts of) {
        return new ExactParts(of.numerator().negate(), of.denominator(), of.twos(), of.fives());
    }

    /** Every order of {@code terms}. */
    private static <T> List<List<T>> orders(List<T> terms) {
        if (terms.isEmpty()) {
            return List.of(List.of());
        }
        List<List<T>> out = new ArrayList<>();
        for (int i = 0; i < terms.size(); i++) {
            List<T> rest = new ArrayList<>(terms);
            T first = rest.remove(i);
            for (List<T> tail : orders(rest)) {
                List<T> one = new ArrayList<>();
                one.add(first);
                one.addAll(tail);
                out.add(one);
            }
        }
        return out;
    }
}
