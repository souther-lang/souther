package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;
import souther.compiler.semantics.TakenAs;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.LocalDate;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a class answers of a run is about the run and the class together: every member it names is
 * in both, and a run outside the calendar, or one the class has no member in, has none.
 *
 * <p>The answer every reader of a class takes — whether the value exists, which values a search
 * offers, which points a border owes — so a member outside the run asked about is a row at a value
 * nothing wrote, and a run cut to the calendar end by end names the calendar's last day for a run
 * that lies wholly after it.
 */
class AClassIsMetWithTheRunItIsAskedAboutTest {

    private static final HeldClass THIRTY_FIRSTS = days(Map.of(TakenAs.DatePart.DAY, only(31)));
    private static final HeldClass EVENS =
            new HeldClass.OfResidues(new Congruences(BigInteger.ZERO, BigInteger.TWO));

    @Test
    void aRunPastEitherEndOfTheCalendarHoldsNoDay() {
        long last = DatePartsLeft.LAST_DAY;
        long first = DatePartsLeft.FIRST_DAY;
        for (NumericDomain.Bounds outside : List.of(between(last + 1, last + 2),
                between(first - 2, first - 1))) {
            for (Towards away : new Towards[] {Towards.ABOVE, Towards.BELOW}) {
                ClassMembers members = THIRTY_FIRSTS.within(outside, away, 3);
                assertEquals(List.of(), members.values(), outside + " " + away);
                assertFalse(members.stoppedShort(), outside + " " + away);
            }
            assertSame(HeldClass.NO_VALUE, THIRTY_FIRSTS.within(outside), outside.toString());
        }
    }

    /** Every member named is inside the run and of the class, from whichever end it is asked. */
    @Test
    void everyMemberNamedIsInTheRunAndOfTheClass() {
        NumericDomain.Bounds run = between(day("2024-01-15"), day("2024-12-15"));
        for (HeldClass held : List.of(THIRTY_FIRSTS, days(Map.of(TakenAs.DatePart.DAY, only(29),
                TakenAs.DatePart.MONTH, only(2))))) {
            for (Towards away : new Towards[] {Towards.ABOVE, Towards.BELOW, null}) {
                for (BigInteger each : held.within(run, away, 20).values()) {
                    assertTrue(held.holds(each), each + " is of " + held);
                    assertTrue(run.admits(new Count(new BigDecimal(each))), each + " is in " + run);
                }
            }
        }
        NumericDomain.Bounds numbers = between(-7, 9);
        for (BigInteger each : EVENS.nearest(BigInteger.ONE, numbers, 20).values()) {
            assertTrue(EVENS.holds(each), each.toString());
            assertTrue(numbers.admits(new Count(new BigDecimal(each))), each.toString());
        }
    }

    /** Members nearest a place come by how far they are, above before below where two are as far. */
    @Test
    void theMembersNearestAPlaceComeByHowFarTheyAre() {
        assertEquals(List.of(BigInteger.valueOf(2), BigInteger.ZERO, BigInteger.valueOf(4),
                        BigInteger.valueOf(-2)),
                EVENS.nearest(BigInteger.ONE, NumericDomain.Bounds.OPEN, 4).values());
    }

    /** A run the class has no member in is no value of it, and one with a member keeps the class. */
    @Test
    void aRunWithNoMemberLeavesNoValue() {
        assertSame(HeldClass.NO_VALUE, EVENS.within(between(1, 1)));
        assertSame(EVENS, EVENS.within(between(1, 2)));
        assertInstanceOf(HeldClass.OfDays.class,
                THIRTY_FIRSTS.within(between(day("2024-01-01"), day("2024-01-31"))));
        assertSame(HeldClass.NO_VALUE,
                THIRTY_FIRSTS.within(between(day("2024-02-01"), day("2024-02-29"))));
    }

    private static HeldClass days(Map<TakenAs.DatePart, NumericDomain.Bounds> parts) {
        return new HeldClass.OfDays(new DatePartsLeft(parts));
    }

    private static NumericDomain.Bounds only(long value) {
        return between(value, value);
    }

    private static NumericDomain.Bounds between(long low, long high) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(low)),
                Endpoint.inclusive(Count.of(high)));
    }

    private static long day(String iso) {
        return LocalDate.parse(iso).toEpochDay();
    }
}
