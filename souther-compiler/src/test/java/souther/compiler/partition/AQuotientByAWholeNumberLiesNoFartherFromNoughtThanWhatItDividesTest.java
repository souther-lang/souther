package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;

import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The numbers a quotient by a whole number comes to: every quotient of a dividend of the range
 * by a divisor of the range other than nought lies in the range answered, and the range answered
 * is no wider than it has to be — reached at both ends by some quotient where every divisor but
 * nought lies on one side of it, and no farther from nought than the farthest dividend where they
 * do not.
 *
 * <p>Enumerated and not argued: every range of dividends from minus three to three, every range
 * of divisors from minus three to three, and no divisor known.
 */
class AQuotientByAWholeNumberLiesNoFartherFromNoughtThanWhatItDividesTest {

    private static final int MOST = 3;

    private static ExactRatio of(long number) {
        return ExactRatio.of(number);
    }

    @Test
    void everyQuotientLiesInTheRangeAnsweredAndTheRangeIsNoWiderThanItHasToBe() {
        for (int least = -MOST; least <= MOST; least++) {
            for (int greatest = least; greatest <= MOST; greatest++) {
                FormRange dividends = new FormRange(of(least), of(greatest));
                askedOf(dividends, null, -MOST, MOST);
                for (int from = -MOST; from <= MOST; from++) {
                    for (int to = from; to <= MOST; to++) {
                        askedOf(dividends, new FormRange(of(from), of(to)), from, to);
                    }
                }
            }
        }
    }

    /** {@code divisors} is null where no divisor is known, and then any from {@code from} to
     *  {@code to} may be. */
    private static void askedOf(FormRange dividends, FormRange divisors, int from, int to) {
        FormRange answered = FormRange.quotientByAWholeNumber(dividends, divisors);
        String asked = dividends + " / " + divisors;
        boolean reachedLeast = false;
        boolean reachedGreatest = false;
        for (long dividend = dividends.least().floor().orNull().longValueExact();
                dividend <= dividends.greatest().floor().orNull().longValueExact(); dividend++) {
            for (int divisor = from; divisor <= to; divisor++) {
                if (divisor == 0) {
                    continue;
                }
                assertTrue(of(dividend).dividedBy(of(divisor))
                                instanceof ExactAnswer.Held<ExactRatio>(ExactRatio quotient)
                                && answered.holds(quotient),
                        dividend + " / " + divisor + " is not in " + answered + " for " + asked);
                ExactRatio quotient = ((ExactAnswer.Held<ExactRatio>)
                        of(dividend).dividedBy(of(divisor))).value();
                reachedLeast |= quotient.equals(answered.least());
                reachedGreatest |= quotient.equals(answered.greatest());
            }
        }
        // Nought divides nothing: what counts is the side of nought the other divisors are on.
        boolean oneSide = divisors != null && (from > 0 || to < 0 || (from == 0 && to > 0)
                || (to == 0 && from < 0));
        if (oneSide) {
            assertTrue(reachedLeast && reachedGreatest, answered + " is wider than " + asked);
        } else {
            ExactRatio farthest = dividends.least().negated().compareTo(dividends.greatest()) > 0
                    ? dividends.least().negated() : dividends.greatest();
            assertTrue(answered.liesWithin(farthest.negated().floor().orNull(),
                    farthest.floor().orNull()), answered + " is wider than " + asked);
        }
    }

    /** Nothing is known of the quotient where nothing is of what it divides. */
    @Test
    void aDividendOfNoKnownRangeLeavesTheQuotientOfNone() {
        assertNull(FormRange.quotientByAWholeNumber(null, null));
        assertNull(FormRange.quotientByAWholeNumber(null, new FormRange(of(2), of(2))));
    }
}
