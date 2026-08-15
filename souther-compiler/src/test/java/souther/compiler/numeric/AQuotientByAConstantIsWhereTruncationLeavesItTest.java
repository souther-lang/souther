package souther.compiler.numeric;

import souther.compiler.numeric.NumericDomain.Bounds;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Where {@code x / k} lies, given where {@code x} does.
 *
 * <p>{@code /} on {@code Int} truncates toward zero (spec §stdlib-int), which is a step function and
 * not an equation — so what is written here is a bound and not a form the affine domain could have
 * carried. Truncation is monotone, so the two ends of the dividend are the two ends of the quotient,
 * exchanged where the divisor is negative.
 */
class AQuotientByAConstantIsWhereTruncationLeavesItTest {

    private static Bounds between(Long min, Long max) {
        return new Bounds(min == null ? null : Endpoint.inclusive(Count.of(min)),
                max == null ? null : Endpoint.inclusive(Count.of(max)));
    }

    private static Count at(Endpoint end) {
        return (Count) end.at();
    }

    /** The dividend's ends, truncated — the whole of what the issue's second example needs of the
     * divide. */
    @Test
    void aDividendAtOrAboveZeroLeavesAQuotientAtOrAboveZero() {
        Bounds quotient = Intervals.truncatingQuotient(between(0L, null), 100);

        assertEquals(Count.of(0), at(quotient.min()));
        assertEquals(true, quotient.min().inclusive());
        assertNull(quotient.max());
    }

    /** Toward zero and not down: {@code -7 / 2} is {@code -3}, so the end below is {@code -3} and
     * not {@code -4}. */
    @Test
    void bothEndsAreTruncatedTowardZero() {
        Bounds quotient = Intervals.truncatingQuotient(between(-7L, 7L), 2);

        assertEquals(Count.of(-3), at(quotient.min()));
        assertEquals(Count.of(3), at(quotient.max()));
    }

    /** Dividing by a negative number reverses the order, so the dividend's ends swap sides. */
    @Test
    void aNegativeDivisorExchangesTheEnds() {
        Bounds quotient = Intervals.truncatingQuotient(between(-7L, 7L), -2);

        assertEquals(Count.of(-3), at(quotient.min()), "7 / -2");
        assertEquals(Count.of(3), at(quotient.max()), "-7 / -2");
    }

    /** An end nothing bounds stays unbounded, on the side the divisor's sign puts it. */
    @Test
    void anUnboundedEndStaysUnboundedOnTheSideTheDivisorPutsIt() {
        Bounds quotient = Intervals.truncatingQuotient(between(10L, null), -5);

        assertNull(quotient.min());
        assertEquals(Count.of(-2), at(quotient.max()));
    }

    /**
     * An end the dividend does not reach is one the quotient is not held away from.
     *
     * <p>A whole-number range records its strict ends on the adjacent count, so this is what a range
     * arriving open would mean rather than a shape the domain hands over today. Widening it is
     * sound — a bound this states can be looser than the true one and never tighter.
     */
    @Test
    void anEndTheDividendDoesNotReachIsWidenedRatherThanSharpened() {
        Bounds openAbove = new Bounds(Endpoint.inclusive(Count.of(0)),
                new Endpoint(Count.of(10), false));

        Bounds quotient = Intervals.truncatingQuotient(openAbove, 5);

        assertEquals(Count.of(2), at(quotient.max()));
        assertEquals(true, quotient.max().inclusive());
    }
}
