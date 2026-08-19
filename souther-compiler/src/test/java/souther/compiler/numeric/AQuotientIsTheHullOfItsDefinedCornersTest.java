package souther.compiler.numeric;

import souther.compiler.numeric.NumericDomain.Bounds;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Where {@code x / y} lies, given where each of them does.
 *
 * <p>{@code /} on {@code Int} truncates toward zero (spec §stdlib-int), which is a step function and
 * not an equation — so what is written here is a bound and not a form the affine domain could have
 * carried. Over a divisor range held away from zero the quotient's extremes are at the corners of
 * the box the two ranges make, and truncation toward zero is non-decreasing, so the corners put
 * through it are still the extremes.
 *
 * <p>What is bounded is the values the operation produced. The one pair inside such a box that it
 * aborts on — {@code Long.MIN_VALUE} over {@code -1}, whose quotient no {@code Int} holds —
 * contributes none, so a range here is a range of what the successful divides came to and says
 * nothing about whether every pair the operands admit is one the operator answers. A zero divisor is
 * the other pair it aborts on, and it is refused here rather than answered for: what a range through
 * zero leaves depends on how its values are spaced, which a range does not say.
 */
class AQuotientIsTheHullOfItsDefinedCornersTest {

    private static Bounds between(Long min, Long max) {
        return new Bounds(min == null ? null : Endpoint.inclusive(Count.of(min)),
                max == null ? null : Endpoint.inclusive(Count.of(max)));
    }

    private static Bounds at(long only) {
        return between(only, only);
    }

    private static Count at(Endpoint end) {
        return (Count) end.at();
    }

    /** The dividend's ends, truncated — the whole of what a percentage of a guarded value needs of
     * the divide. */
    @Test
    void aDividendAtOrAboveZeroLeavesAQuotientAtOrAboveZero() {
        Bounds quotient = Intervals.truncatingQuotient(between(0L, null), at(100));

        assertEquals(Count.of(0), at(quotient.min()));
        assertEquals(true, quotient.min().inclusive());
        assertNull(quotient.max());
    }

    /** Toward zero and not down: {@code -7 / 2} is {@code -3}, so the end below is {@code -3} and
     * not {@code -4}. */
    @Test
    void bothEndsAreTruncatedTowardZero() {
        Bounds quotient = Intervals.truncatingQuotient(between(-7L, 7L), at(2));

        assertEquals(Count.of(-3), at(quotient.min()));
        assertEquals(Count.of(3), at(quotient.max()));
    }

    /** Dividing by a negative number reverses the order, so the dividend's ends swap sides. */
    @Test
    void aNegativeDivisorExchangesTheEnds() {
        Bounds quotient = Intervals.truncatingQuotient(between(-7L, 7L), at(-2));

        assertEquals(Count.of(-3), at(quotient.min()), "7 / -2");
        assertEquals(Count.of(3), at(quotient.max()), "-7 / -2");
    }

    /** An end nothing bounds stays unbounded, on the side the divisor's sign puts it. */
    @Test
    void anUnboundedEndStaysUnboundedOnTheSideTheDivisorPutsIt() {
        Bounds quotient = Intervals.truncatingQuotient(between(10L, null), at(-5));

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
    void anEndAnOperandDoesNotReachIsWidenedRatherThanSharpened() {
        Bounds openAbove = new Bounds(Endpoint.inclusive(Count.of(0)),
                new Endpoint(Count.of(10), false));

        Bounds quotient = Intervals.truncatingQuotient(openAbove, at(5));

        assertEquals(Count.of(2), at(quotient.max()));
        assertEquals(true, quotient.max().inclusive());
    }

    /**
     * A divisor the path holds between two counts, which is what a day count apportions by.
     *
     * <p>The four corners and not two: dividing by the near end of the divisor is one end of the
     * answer and by the far end is the other, so a divisor that is a range is read exactly as a
     * factor of a product is.
     */
    @Test
    void aDivisorHeldBetweenTwoCountsIsReadOffTheFourCorners() {
        Bounds quotient = Intervals.truncatingQuotient(between(0L, 100L), between(1L, 31L));

        assertEquals(Count.of(0), at(quotient.min()), "0 / 31");
        assertEquals(Count.of(100), at(quotient.max()), "100 / 1");
    }

    /** A divisor range wholly below zero puts the quotient on the other side, both ends of it. */
    @Test
    void aDivisorRangeBelowZeroExchangesTheEndsAsAWrittenNegativeDoes() {
        Bounds quotient = Intervals.truncatingQuotient(between(0L, 100L), between(-31L, -1L));

        assertEquals(Count.of(-100), at(quotient.min()), "100 / -1");
        assertEquals(Count.of(0), at(quotient.max()), "0 / -1");
    }

    /**
     * A divisor unbounded above sends the dividend's ends toward zero, and the end that is reached
     * is the one the near end of the divisor gives.
     *
     * <p>A dividend below zero divided by ever larger divisors comes up to zero and reaches it, at
     * every divisor past the dividend's own magnitude. So the end above is zero and not the
     * {@code -1} the two written ends would give.
     */
    @Test
    void aDivisorUnboundedAboveSendsTheQuotientToZero() {
        Bounds quotient = Intervals.truncatingQuotient(between(-10L, -1L), between(1L, null));

        assertEquals(Count.of(-10), at(quotient.min()), "-10 / 1");
        assertEquals(Count.of(0), at(quotient.max()), "-1 / a divisor past every value");
    }

    /**
     * Two ends past every value make no corner, and nothing is lost by leaving it out.
     *
     * <p>A divisor held away from zero has at most one end past every value — both would be a range
     * through zero — so the dividend's own unbounded end meets the divisor's finite end as well, and
     * reaches the same side there. Here the answer is unbounded above through {@code x / 1}, and
     * bounded below at zero through the divisor's other end, which a reading that gave up on the
     * whole box would have lost.
     */
    @Test
    void aCornerWhereBothEndsRunPastEveryValueIsNotACandidate() {
        Bounds quotient = Intervals.truncatingQuotient(between(0L, null), between(1L, null));

        assertEquals(Count.of(0), at(quotient.min()));
        assertNull(quotient.max());
    }

    /**
     * A range admitting zero is not a divisor to read, and this says so rather than answering.
     *
     * <p>What it would leave is not something a range says. Over the whole numbers {@code [0, 5]}
     * divides by one at the nearest and the successful quotients are bounded; over a dense order
     * there is no nearest and they are not. Answering a range here would state the second of those
     * as arithmetic, and it is the caller — which knows how its values are spaced and what its rule
     * needs established — that has the question.
     */
    @Test
    void aRangeAdmittingZeroIsRefusedRatherThanAnswered() {
        assertThrows(IllegalArgumentException.class,
                () -> Intervals.truncatingQuotient(between(1L, 10L), between(0L, 5L)));
    }

    /**
     * A divisor kept off zero only by not reaching it still runs the quotient past every value.
     *
     * <p>This is the case the ends really do settle: nothing between them bounds how small the
     * divisor is, so the quotient has no end that way whatever the spacing. A discrete carrier does
     * not arrive here like this — a strict bound on one is sharpened onto the adjacent count — and
     * the arithmetic is written for the range and not for the carrier that happened to hand it over.
     */
    @Test
    void aDivisorOpenAtZeroIsUnboundedTheWayItsMagnitudeRuns() {
        Bounds openAtZero = new Bounds(Endpoint.exclusive(Count.of(0)),
                Endpoint.inclusive(Count.of(5)));

        Bounds quotient = Intervals.truncatingQuotient(between(2L, 3L), openAtZero);

        assertEquals(Count.of(0), at(quotient.min()), "2 / 5");
        assertNull(quotient.max());
    }

    /**
     * Which side of zero the divisor is on is read off where its lower end is, and not off whether
     * that end is one of its own values.
     *
     * <p>A range below zero whose ends are both strict is on the same side as one whose ends are
     * not. Read the other way round — an end the range does not reach taken for an end at zero — the
     * divisor comes out above zero and both ends of the answer land on the wrong side of it.
     */
    @Test
    void aDivisorBelowZeroIsBelowItWhicheverOfItsEndsAreReached() {
        Bounds strictlyBelow = new Bounds(Endpoint.exclusive(Count.of(-5)),
                Endpoint.exclusive(Count.of(-1)));

        Bounds quotient = Intervals.truncatingQuotient(between(10L, 20L), strictlyBelow);

        assertEquals(Count.of(-20), at(quotient.min()), "20 / -1");
        assertEquals(Count.of(-2), at(quotient.max()), "10 / -5");
    }

    /**
     * The one pair whose quotient no {@code Int} holds is not held out of the answer.
     *
     * <p>{@code Long.MIN_VALUE / -1} aborts (spec §stdlib-int), so it produces no value and a range
     * taking in the number the arithmetic gives there still covers every value the operation
     * produced. Holding it out would be a definedness analysis inside an interval transfer, and the
     * two would then have to be told apart in an answer that has room for one.
     */
    @Test
    void thePairThatAbortsIsNotHeldOutOfTheHull() {
        Bounds quotient = Intervals.truncatingQuotient(at(Long.MIN_VALUE), at(-1));

        BigDecimal past = BigDecimal.valueOf(Long.MAX_VALUE).add(BigDecimal.ONE);
        assertEquals(Count.of(past), at(quotient.min()));
        assertEquals(Count.of(past), at(quotient.max()));
    }

    /**
     * A range holding no value is not a divisor to read, and this says so rather than answering.
     *
     * <p>Whether the rule has a divisor at all is decided before this is asked. Answered here, "no
     * such operand" and "no bound to give" would be one value, and the caller that has to tell them
     * apart is exactly the one that knows which it has.
     */
    @Test
    void aRangeHoldingNoValueIsRefusedRatherThanAnswered() {
        Bounds crossed = new Bounds(Endpoint.inclusive(Count.of(5)),
                Endpoint.inclusive(Count.of(1)));

        assertThrows(IllegalArgumentException.class,
                () -> Intervals.truncatingQuotient(between(0L, 10L), crossed));
    }
}
