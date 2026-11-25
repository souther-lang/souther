package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The least whole number a lower end admits and the greatest an upper end admits, held to the
 * whole numbers counted out on either side of it.
 *
 * <p>Asked of a cut and of an end at a count, which is read through the cut: the two answer one
 * question, and where they were worked out apart one of them treated an excluded whole end as
 * included. Ends at a whole number and between two, on both sides of nought, admitted and not.
 */
class TheWholeNumbersAnEndAdmitsAreTheOnesPastItTest {

    private static final String[] ENDS = {"-2.5", "-2", "0", "0.3", "3"};

    @Test
    void theLeastAndTheGreatestAreTheFirstOnesCountedPastTheEnd() {
        for (String written : ENDS) {
            ExactRatio at = ExactRatio.of(new BigDecimal(written));
            for (boolean inclusive : new boolean[] {true, false}) {
                ExactCut cut = new ExactCut(at, inclusive);
                Endpoint end = new Endpoint(Count.of(new BigDecimal(written)), inclusive);
                BigInteger least = counted(at, inclusive, true);
                BigInteger greatest = counted(at, inclusive, false);
                String asked = (inclusive ? "at or past " : "past ") + written;
                assertEquals(least, cut.leastWhole().orNull(), () -> "the least " + asked);
                assertEquals(greatest, cut.greatestWhole().orNull(),
                        () -> "the greatest " + asked);
                assertEquals(least, end.wholeAdmitted(true), () -> "the end's least " + asked);
                assertEquals(greatest, end.wholeAdmitted(false),
                        () -> "the end's greatest " + asked);
                assertEquals(cut, end.asCut(), () -> "the end's cut " + asked);
                assertEquals(at, end.exactly(), () -> "the end's number " + asked);
            }
        }
    }

    /** At either end of the scale. A whole number no host writes has no whole number past it to
     *  answer with, and says so rather than throwing; the least positive power has nought below
     *  it and one above, whichever way it is admitted. */
    @Test
    void anEndAtEitherEndOfTheScaleIsAnsweredOrSaysWhyNot() {
        ExactRatio unwritten = ExactRatio.tenTo(Long.MAX_VALUE);
        for (boolean inclusive : new boolean[] {true, false}) {
            ExactCut far = new ExactCut(unwritten, inclusive);
            assertInstanceOf(ExactAnswer.Unheld.class, far.leastWhole());
            assertInstanceOf(ExactAnswer.Unheld.class, far.greatestWhole());
            ExactCut near = new ExactCut(ExactRatio.tenTo(Long.MIN_VALUE), inclusive);
            assertEquals(BigInteger.ONE, near.leastWhole().orNull());
            assertEquals(BigInteger.ZERO, near.greatestWhole().orNull());
        }
    }

    /** The first whole number from -10 upwards that stands above {@code at} — or from 10
     *  downwards, below it — at it counted where {@code inclusive}. */
    private static BigInteger counted(ExactRatio at, boolean inclusive, boolean upwards) {
        for (int step = 0; step <= 20; step++) {
            BigInteger whole = BigInteger.valueOf(upwards ? -10 + step : 10 - step);
            int order = ExactRatio.of(whole).compareTo(at);
            if (upwards ? order > 0 || (inclusive && order == 0)
                    : order < 0 || (inclusive && order == 0)) {
                return whole;
            }
        }
        throw new AssertionError("no whole number from -10 to 10 is past " + at);
    }
}
