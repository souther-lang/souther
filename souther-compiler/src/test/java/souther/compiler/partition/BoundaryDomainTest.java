package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTimes;
import souther.compiler.numeric.Dates;

import java.math.BigDecimal;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Asking for the value beside a boundary is asking the carrier.
 *
 * <p>{@code cost <= 100000} wants 100001 tried as well, and that count exists because the carrier
 * steps in whole numbers. A decimal has no next count, and inventing one — 100000.01, or whatever
 * scale happens to be in the compiler — would test a rule the model never stated.
 *
 * <p>Asked of the carrier and answered in counts, both ways. Answered about values, each of these had
 * to recognise the shape a value of its own carrier takes before it could step at all — so a step
 * over the wrong kind of value came back as no neighbour rather than as a build failure, and the
 * carrier that would have said which was right there.
 */
class BoundaryDomainTest {

    private static Count day(String iso) {
        return Dates.dayOf(iso);
    }

    @Test
    void aCarrierThatStepsHasBothNeighbours() {
        Count hundred = Count.of(100);

        assertEquals(Optional.of(Count.of(101)), BoundaryDomain.on(Carrier.WHOLE).successor(hundred));
        assertEquals(Optional.of(Count.of(99)), BoundaryDomain.on(Carrier.WHOLE).predecessor(hundred));
    }

    /**
     * A step off the end of what a carrier counts is not a neighbour.
     *
     * <p>Refused by the carrier rather than by this: what a whole number stops at is a fact about the
     * carrier, and every caller that steps a count reaches the same answer through it.
     */
    @Test
    void aCountAtTheEdgeOfWhatTheCarrierHoldsHasNoneOnThatSide() {
        assertTrue(BoundaryDomain.on(Carrier.WHOLE).successor(Count.of(Long.MAX_VALUE)).isEmpty());
        assertTrue(BoundaryDomain.on(Carrier.WHOLE).predecessor(Count.of(Long.MIN_VALUE)).isEmpty());
    }

    /** The restraint that matters: no epsilon is invented. A decimal is the carrier with no smallest
     *  step this language names, and since a `DateTime` is held to the second it is the only one. */
    @Test
    void aDenseCarrierHasNoNeighbourToGive() {
        Count amount = Count.of(new BigDecimal("100000"));

        assertTrue(BoundaryDomain.on(Carrier.DENSE).successor(amount).isEmpty());
        assertTrue(BoundaryDomain.on(Carrier.DENSE).predecessor(amount).isEmpty());
    }

    /** A date-time steps, and by a second. This was the other dense carrier while a `DateTime`
     *  carried nanoseconds and the step it moved in was a decision nobody had taken
     *  (spec §a-local-temporal-is-held-to-the-second). */
    @Test
    void aMomentStepsBySecondsEitherWay() {
        Count at = DateTimes.secondOf("2026-08-01T00:00:01");

        assertEquals(Optional.of(DateTimes.secondOf("2026-08-01T00:00:02")),
                BoundaryDomain.on(Carrier.MOMENT).successor(at));
        assertEquals(Optional.of(DateTimes.secondOf("2026-08-01T00:00:00")),
                BoundaryDomain.on(Carrier.MOMENT).predecessor(at));
    }

    @Test
    void aPositionOnNoCarrierAnswersNothing() {
        assertTrue(BoundaryDomain.on(null).successor(Count.of(1)).isEmpty());
        assertTrue(BoundaryDomain.on(null).predecessor(Count.of(1)).isEmpty());
    }

    /** A date's neighbours are whole days, so what steps is the day it counts to. */
    @Test
    void aDateStepsInWholeDays() {
        Count first = day("2026-01-01");
        Count second = day("2026-01-02");
        BoundaryDomain dates = BoundaryDomain.on(Carrier.DATE);

        assertEquals(Optional.of(second), dates.successor(first));
        assertEquals(Optional.of(first), dates.predecessor(second));
    }
}
