package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A whole number other than nought is at least one from nought, so a quotient by one lies no
 * farther from nought than what it divides — and the range of the quotient is the one symmetric
 * about nought that the dividend's farthest end reaches.
 *
 * <p>Enumerated and not argued: every range of dividends from minus six to six, every divisor from
 * minus eight to eight but nought, every dividend of the range. The quotient each makes is in the
 * range answered, and the range answered is no wider than the farthest dividend.
 */
class AQuotientByAWholeNumberLiesNoFartherFromNoughtThanWhatItDividesTest {

    private static ExactRatio of(long number) {
        return ExactRatio.of(number);
    }

    @Test
    void everyQuotientOfARangeByAWholeNumberLiesInTheRangeAnswered() {
        int asked = 0;
        for (int least = -6; least <= 6; least++) {
            for (int greatest = least; greatest <= 6; greatest++) {
                FormRange answered = FormRange.quotientByAWholeNumber(
                        new FormRange(of(least), of(greatest)));
                int farthest = Math.max(Math.abs(least), Math.abs(greatest));
                assertEquals(of(-farthest), answered.least(), least + ".." + greatest);
                assertEquals(of(farthest), answered.greatest(), least + ".." + greatest);
                for (int dividend = least; dividend <= greatest; dividend++) {
                    for (int divisor = -8; divisor <= 8; divisor++) {
                        if (divisor == 0) {
                            continue;
                        }
                        asked++;
                        assertTrue(of(dividend).dividedBy(of(divisor))
                                        instanceof ExactAnswer.Held<ExactRatio>(ExactRatio quotient)
                                        && quotient.compareTo(answered.least()) >= 0
                                        && quotient.compareTo(answered.greatest()) <= 0,
                                dividend + " / " + divisor + " is not in " + answered);
                    }
                }
            }
        }
        assertTrue(asked > 1000, "only " + asked + " quotients were asked");
    }

    /** Nothing is known of the quotient where nothing is of what it divides. */
    @Test
    void aDividendOfNoKnownRangeLeavesTheQuotientOfNone() {
        assertNull(FormRange.quotientByAWholeNumber(null));
    }
}
