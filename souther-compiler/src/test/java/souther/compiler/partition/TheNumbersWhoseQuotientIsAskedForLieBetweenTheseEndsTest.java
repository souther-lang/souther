package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.semantics.TakenAs;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The ends a solving looks between hold every number whose quotient is one of the ones asked for.
 *
 * <p><b>The one thing the ends owe.</b> A value is admitted by dividing it and asking the sets, so
 * ends wider than the truth cost a number tried and nothing else — and ends narrower than the truth
 * are a row that exists and is never offered, which no membership can put back. So what is checked
 * here is that nothing is left out, over the signs a divisor and a quotient can be: truncation
 * counts toward zero, so the run a quotient answers sits one side of nought for a positive number
 * and the other side for a negative one, and the run around nought is as wide as both.
 *
 * <p>Read against the reading's own division rather than against a second spelling of it, which is
 * the only thing that makes this a check: the arithmetic under test works out where the numbers
 * are, and {@link TakenAs.TheTruncatingQuotient#quotientOf} says what one of them answers.
 */
class TheNumbersWhoseQuotientIsAskedForLieBetweenTheseEndsTest {

    /** Divisors either side of nought, and one that is neither two nor three. */
    private static final List<String> DIVISORS = List.of("2", "3", "7", "-2", "-3", "-7");

    /** As far either way as a walk of this test can be asked to go. */
    private static final int FAR = 60;

    /**
     * Every number whose quotient is exactly the one asked for lies between the ends.
     *
     * <p>The case a point of a border asks: one number for the quotient, and the run of the place
     * that answers it.
     */
    @Test
    void everyNumberWhoseQuotientIsThatOneLiesBetweenTheEnds() {
        List<String> outside = new ArrayList<>();
        for (String divisor : DIVISORS) {
            BigDecimal by = new BigDecimal(divisor);
            for (int at = -FAR; at <= FAR; at++) {
                BigDecimal value = BigDecimal.valueOf(at);
                BigDecimal quotient = TakenAs.TheTruncatingQuotient.quotientOf(value, by);
                NumericDomain.Bounds lies = TermRealizations.numbersWhoseQuotientLiesIn(
                        exactly(quotient), by);
                if (!holds(lies, value)) {
                    outside.add(at + " / " + divisor + " is " + quotient
                            + ", which is asked for by " + lies);
                }
            }
        }
        assertEquals(List.of(), outside,
                "every number whose quotient is the one asked for lies between the ends");
    }

    /**
     * And every number whose quotient is one of a run of them does.
     *
     * <p>The case a class asks, at every arrangement of the two ends: shut either way, open either
     * way, and either end left off altogether.
     */
    @Test
    void everyNumberWhoseQuotientIsOneOfARunLiesBetweenTheEnds() {
        List<String> outside = new ArrayList<>();
        for (String divisor : DIVISORS) {
            BigDecimal by = new BigDecimal(divisor);
            for (int low = -4; low <= 4; low++) {
                for (int high = low; high <= 4; high++) {
                    for (boolean shutBelow : List.of(true, false)) {
                        for (boolean shutAbove : List.of(true, false)) {
                            outside.addAll(leftOutOf(by, new NumericDomain.Bounds(
                                    new Endpoint(count(low), shutBelow),
                                    new Endpoint(count(high), shutAbove))));
                        }
                    }
                }
            }
            outside.addAll(leftOutOf(by, new NumericDomain.Bounds(
                    Endpoint.inclusive(count(2)), null)));
            outside.addAll(leftOutOf(by, new NumericDomain.Bounds(
                    null, Endpoint.inclusive(count(-2)))));
        }
        assertEquals(List.of(), outside,
                "every number whose quotient is one of the run lies between the ends");
    }

    /** The numbers this run of quotients asks for that the ends leave out, which is none of
     *  them. */
    private static List<String> leftOutOf(BigDecimal by, NumericDomain.Bounds quotients) {
        NumericDomain.Bounds lies = TermRealizations.numbersWhoseQuotientLiesIn(quotients, by);
        assertNotNull(lies, () -> "a run of quotients is a run of the place: " + quotients);
        List<String> outside = new ArrayList<>();
        for (int at = -FAR; at <= FAR; at++) {
            BigDecimal value = BigDecimal.valueOf(at);
            if (holds(quotients, TakenAs.TheTruncatingQuotient.quotientOf(value, by))
                    && !holds(lies, value)) {
                outside.add(at + " / " + by + " is one of " + quotients
                        + ", which is asked for by " + lies);
            }
        }
        return outside;
    }

    /** That one number and no other, as the ends a caller of the arithmetic hands over. */
    private static NumericDomain.Bounds exactly(BigDecimal number) {
        return new NumericDomain.Bounds(
                Endpoint.inclusive(count(number)), Endpoint.inclusive(count(number)));
    }

    private static Place count(long at) {
        return count(BigDecimal.valueOf(at));
    }

    private static Place count(BigDecimal at) {
        return Count.of(at);
    }

    /** Whether a number is between two ends, which is what the ends are for and is not read off
     *  them anywhere else in this test. */
    private static boolean holds(NumericDomain.Bounds ends, BigDecimal at) {
        if (ends.min() != null) {
            int against = at.compareTo(((Count) ends.min().at()).at());
            if (against < 0 || (against == 0 && !ends.min().inclusive())) {
                return false;
            }
        }
        if (ends.max() != null) {
            int against = at.compareTo(((Count) ends.max().at()).at());
            if (against > 0 || (against == 0 && !ends.max().inclusive())) {
                return false;
            }
        }
        return true;
    }
}
