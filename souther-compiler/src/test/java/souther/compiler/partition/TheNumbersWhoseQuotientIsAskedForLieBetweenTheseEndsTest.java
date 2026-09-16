package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.semantics.Arithmetic;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The ends a solving looks between are exactly the numbers whose quotient is one of those asked
 * for.
 *
 * <p><b>Both halves, because each is a different defect.</b> Ends narrower than the truth are a row
 * that exists and is never offered, which no membership can put back. Ends wider than the truth are
 * numbers the demands turn down, and the figure the walk holds to counts the numbers it admits — so
 * a walk through them steps without spending anything, and a divisor of a billion is a billion
 * steps nobody bounded.
 *
 * <p>Over the signs a divisor and a quotient can be, since truncation counts toward zero: the run a
 * quotient answers sits one side of nought for a positive number and the other side for a negative
 * one, and the run around nought is as wide as both. And over a divisor wide enough that the second
 * defect would be a compile nobody waits for.
 *
 * <p>Read against the arithmetic's own division rather than against a second spelling of it, which
 * is the only thing that makes this a check: the ends under test work out where the numbers are,
 * and {@link Arithmetic.ATruncatingQuotient#quotientOf} says what one of them answers. That
 * division is itself held to the one the runtime computes, so a compiler agreeing with itself is
 * not what passes here.
 */
class TheNumbersWhoseQuotientIsAskedForLieBetweenTheseEndsTest {

    /** Divisors either side of nought, and one that is neither two nor three. */
    private static final List<String> DIVISORS = List.of("2", "3", "7", "-2", "-3", "-7");

    /** As far either way as a walk of this test can be asked to go. */
    private static final int FAR = 60;

    /**
     * A divisor wide enough that a walk over ends one quotient too wide would not come back.
     *
     * <p>Not a number a model is unlikely to hold: a whole number of this language is a signed
     * sixty-four bit count, so this is an ordinary constant to divide by. What makes it the case
     * to check is the width, since the numbers between an end and the truth are as many as the
     * divisor.
     */
    private static final String A_WIDE_DIVISOR = "1000000000";

    /**
     * Every number whose quotient is exactly the one asked for lies between the ends.
     *
     * <p>The case a point of a border asks: one number for the quotient, and the run of the place
     * that answers it.
     */
    @Test
    void everyNumberWhoseQuotientIsThatOneLiesBetweenTheEnds() {
        List<String> outside = new ArrayList<>();
        int checked = 0;
        for (String divisor : DIVISORS) {
            BigDecimal by = new BigDecimal(divisor);
            for (int at = -FAR; at <= FAR; at++) {
                BigDecimal value = BigDecimal.valueOf(at);
                BigDecimal quotient = Arithmetic.ATruncatingQuotient.quotientOf(value, by);
                NumericDomain.Bounds lies = TermRealizations.numbersWhoseQuotientLiesIn(
                        exactly(quotient), by);
                checked++;
                if (!holds(lies, value)) {
                    outside.add(at + " / " + divisor + " is " + quotient
                            + ", which is asked for by " + lies);
                }
            }
        }
        assertEquals(List.of(), outside,
                "every number whose quotient is the one asked for lies between the ends");
        assertEquals(DIVISORS.size() * (2 * FAR + 1), checked,
                "and every number of every divisor was the one asked about");
    }

    /**
     * And the division the ends are worked out from is the one the runtime computes.
     *
     * <p>What makes the rest of this a check rather than two readings of one belief. The ends are
     * held to a division here, and if that division were not the operator's the whole of this
     * would agree with itself and a row would still stand at a number it does not read back as.
     * So the arithmetic is asked against {@code IntMath}, which is what a compiled program runs.
     */
    @Test
    void theDivisionTheEndsAreWorkedOutFromIsTheOneAProgramRuns() {
        List<String> apart = new ArrayList<>();
        for (String divisor : DIVISORS) {
            long by = Long.parseLong(divisor);
            for (long at = -FAR; at <= FAR; at++) {
                BigDecimal read = Arithmetic.ATruncatingQuotient.quotientOf(
                        BigDecimal.valueOf(at), BigDecimal.valueOf(by));
                long run = souther.runtime.IntMath.divideExact(at, by);
                if (read.compareTo(BigDecimal.valueOf(run)) != 0) {
                    apart.add(at + " / " + by + " is " + read + " here and " + run + " at run time");
                }
            }
        }
        assertEquals(List.of(), apart, "the quotient this compiler works with is the one a program"
                + " computes");
    }

    /**
     * And the ends hold nothing else: the numbers just outside them answer a quotient that was not
     * asked for.
     *
     * <p>The half a soundness check cannot see. Ends a whole quotient too wide hold every number
     * between the truth and themselves, and the figure the walk holds to counts the numbers it
     * admits rather than the ones it steps over — so the walk spends nothing on them and a wide
     * divisor is a wide walk nobody bounded. Checked at the ends themselves and at the number one
     * step outside each, which is where the widening would show at any divisor.
     */
    @Test
    void nothingJustOutsideTheEndsAnswersAQuotientThatWasAskedFor() {
        List<String> inside = new ArrayList<>();
        List<String> divisors = List.of("2", "3", "-2", "-3", A_WIDE_DIVISOR,
                "-" + A_WIDE_DIVISOR);
        int checked = 0;
        for (String divisor : divisors) {
            BigDecimal by = new BigDecimal(divisor);
            for (NumericDomain.Bounds asked : everyArrangementOfTwoEnds()) {
                NumericDomain.Bounds lies =
                        TermRealizations.numbersWhoseQuotientLiesIn(asked, by);
                assertNotNull(lies.min(), () -> "a run of quotients is shut below: " + lies);
                assertNotNull(lies.max(), () -> "and shut above: " + lies);
                BigDecimal low = ((Count) lies.min().at()).at();
                BigDecimal high = ((Count) lies.max().at()).at();
                checked++;
                // A run of quotients holding no whole number is a run of the place holding none,
                // and ends that have crossed are how a walk of whole numbers says so. Nothing is
                // attained there, so there is nothing to ask about the ends themselves.
                if (!holdsAWholeNumber(asked)) {
                    if (low.compareTo(high) <= 0) {
                        inside.add(asked + " holds no whole quotient, and " + lies
                                + " holds numbers");
                    }
                    continue;
                }
                inside.addAll(readsBack(low, by, asked, true));
                inside.addAll(readsBack(high, by, asked, true));
                inside.addAll(readsBack(low.subtract(BigDecimal.ONE), by, asked, false));
                inside.addAll(readsBack(high.add(BigDecimal.ONE), by, asked, false));
            }
        }
        assertEquals(List.of(), inside,
                "the ends are the numbers the quotients asked for and no others");
        assertEquals(divisors.size() * everyArrangementOfTwoEnds().size(), checked,
                "and every arrangement of the ends was asked about, for every divisor");
    }

    /**
     * The ends a run of quotients comes in: shut and open either way, and ends that name no whole
     * number at all.
     *
     * <p><b>The open ends are the case that matters.</b> A quotient end read one number further out
     * for the sake of a simpler reading of exclusivity is a run of the place wider by a whole
     * divisor, and a shut end read the same way is not — so a check over shut ends alone passes
     * either way. An end naming no whole number is the other reading, since a quotient of whole
     * numbers is one.
     */
    private static List<NumericDomain.Bounds> everyArrangementOfTwoEnds() {
        List<NumericDomain.Bounds> out = new ArrayList<>();
        for (String low : List.of("-3", "0", "1")) {
            for (String high : List.of("1", "5")) {
                for (boolean shutBelow : List.of(true, false)) {
                    for (boolean shutAbove : List.of(true, false)) {
                        out.add(new NumericDomain.Bounds(
                                new Endpoint(count(new BigDecimal(low)), shutBelow),
                                new Endpoint(count(new BigDecimal(high)), shutAbove)));
                    }
                }
            }
        }
        out.add(new NumericDomain.Bounds(
                Endpoint.inclusive(count(new BigDecimal("0.5"))),
                Endpoint.inclusive(count(new BigDecimal("4.5")))));
        out.add(new NumericDomain.Bounds(
                Endpoint.exclusive(count(new BigDecimal("-2.5"))),
                Endpoint.exclusive(count(new BigDecimal("2.5")))));
        return out;
    }

    /** Whether any whole number is between these ends, which is what a quotient of whole numbers
     *  can be. */
    private static boolean holdsAWholeNumber(NumericDomain.Bounds ends) {
        for (int at = -FAR; at <= FAR; at++) {
            if (holds(ends, BigDecimal.valueOf(at))) {
                return true;
            }
        }
        return false;
    }

    /** What to say where dividing {@code at} lands somewhere other than {@code expected} says. */
    private static List<String> readsBack(BigDecimal at, BigDecimal by,
                                          NumericDomain.Bounds asked, boolean expected) {
        boolean answers = holds(asked, Arithmetic.ATruncatingQuotient.quotientOf(at, by));
        return answers == expected ? List.of()
                : List.of(at + " / " + by + " is "
                        + Arithmetic.ATruncatingQuotient.quotientOf(at, by) + ", and " + asked
                        + (expected ? " was asked for and the end does not hold it"
                                : " was not asked for and the end holds it"));
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
            if (holds(quotients, Arithmetic.ATruncatingQuotient.quotientOf(value, by))
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
