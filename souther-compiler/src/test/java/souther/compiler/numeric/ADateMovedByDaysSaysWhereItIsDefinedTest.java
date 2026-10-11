package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A chain of shifts of a date is a pair: the days it moves a date by, and the dates at which every
 * step of it is defined. The pair is closed under one more shift, and a chain that moves a date by
 * nothing is the date only where it is defined everywhere.
 */
class ADateMovedByDaysSaysWhereItIsDefinedTest {

    private static final long FIRST = LocalDate.MIN.toEpochDay();
    private static final long LAST = LocalDate.MAX.toEpochDay();

    @Test
    void shiftsAddUp() {
        DateTranslation chain = DateTranslation.none().thenAddDays(31).thenAddDays(-1);

        assertEquals(30, chain.offsetDays());
        assertEquals(DateTranslation.none().thenAddDays(30).offsetDays(), chain.offsetDays());
    }

    @Test
    void aSingleShiftIsDefinedWhereItsResultIsADate() {
        DateTranslation one = DateTranslation.none().thenAddDays(1);

        assertEquals(FIRST, one.first());
        assertEquals(LAST - 1, one.last());
        assertTrue(one.definedAt(LAST - 1));
        assertFalse(one.definedAt(LAST));
        assertTrue(one.isOneShift());

        DateTranslation back = DateTranslation.none().thenAddDays(-1);
        assertEquals(FIRST + 1, back.first());
        assertEquals(LAST, back.last());
    }

    /**
     * Moved and moved back moves nothing, and is defined at one date fewer than the date is: the
     * first move takes the last date off the end of the calendar.
     */
    @Test
    void aShiftUndoneMovesNothingAndIsDefinedWhereItsFirstStepIs() {
        DateTranslation undone = DateTranslation.none().thenAddDays(1).thenAddDays(-1);

        assertEquals(0, undone.offsetDays());
        assertEquals(FIRST, undone.first());
        assertEquals(LAST - 1, undone.last());
        assertFalse(undone.isNone());
        assertFalse(undone.isOneShift());
        assertFalse(undone.definedAt(LAST));
    }

    @Test
    void theOtherWayRoundLosesTheFirstDateInstead() {
        DateTranslation undone = DateTranslation.none().thenAddDays(-1).thenAddDays(1);

        assertEquals(FIRST + 1, undone.first());
        assertEquals(LAST, undone.last());
    }

    @Test
    void aShiftThatMovesNothingAnywhereIsTheIdentity() {
        assertSame(ValueTransformation.NONE,
                ValueTransformation.of(DateTranslation.none().thenAddDays(0)));
        assertInstanceOf(ValueTransformation.DateShift.class,
                ValueTransformation.of(DateTranslation.none().thenAddDays(1).thenAddDays(-1)));
    }

    @Test
    void twoChainsWithOneOffsetAreTwoShiftsWhereTheyAreDefinedApart() {
        ValueTransformation plain = ValueTransformation.of(DateTranslation.none().thenAddDays(0));
        ValueTransformation undone = ValueTransformation
                .of(DateTranslation.none().thenAddDays(1).thenAddDays(-1));

        assertNotEquals(plain, undone);
        assertEquals(undone, ValueTransformation
                .of(DateTranslation.none().thenAddDays(1).thenAddDays(-1)));
    }

    @Test
    void aChainNoDateIsDefinedAtIsNoChain() {
        // Past the end of the calendar from every date there is, and past what a count holds.
        assertNull(DateTranslation.none().thenAddDays(LAST - FIRST + 1));
        assertNull(DateTranslation.none().thenAddDays(Long.MAX_VALUE));
        assertNull(DateTranslation.none().thenAddDays(Long.MIN_VALUE));
    }

    @Test
    void anOriginIsTheDateAMovedDateCameFromWhereThereIsOne() {
        DateTranslation one = DateTranslation.none().thenAddDays(1);

        assertEquals(10L, one.originOf(11));
        assertNull(one.originOf(LAST + 1));
        assertNull(DateTranslation.none().thenAddDays(1).thenAddDays(-1).originOf(LAST));
    }

    @Test
    void aChainIsWrittenByWhereItIsDefinedOnlyWhereTheDaysAloneWouldNotSayIt() {
        assertEquals("+1 days", DateTranslation.none().thenAddDays(1).toString());
        assertEquals("-1 days", DateTranslation.none().thenAddDays(-1).toString());
        assertTrue(DateTranslation.none().thenAddDays(1).thenAddDays(-1).toString()
                .startsWith("+0 days, defined from "));
    }
}
