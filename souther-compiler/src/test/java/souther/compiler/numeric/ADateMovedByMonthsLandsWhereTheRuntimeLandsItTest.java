package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.time.DateTimeException;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Where a date lands moved by whole months is where the runtime's move lands it, which is
 * {@code LocalDate.plusMonths}: on the date's own day or the last of a shorter month, and nowhere
 * past the calendar. And the month it lands in is the one {@link CalendarMonths#monthLandedIn}
 * says, which is what a reader of the month reads.
 */
class ADateMovedByMonthsLandsWhereTheRuntimeLandsItTest {

    /** A month shorter than the day is landed on at its last day, which a leap year moves. */
    @Test
    void aDayPastTheMonthItLandsInIsItsLastDay() {
        assertEquals(LocalDate.of(2025, 2, 28), CalendarMonths.movedBy(1, LocalDate.of(2025, 1, 31)));
        assertEquals(LocalDate.of(2024, 2, 29), CalendarMonths.movedBy(1, LocalDate.of(2024, 1, 31)));
        assertEquals(LocalDate.of(2100, 2, 28), CalendarMonths.movedBy(1, LocalDate.of(2100, 1, 31)));
        assertEquals(LocalDate.of(2000, 2, 29), CalendarMonths.movedBy(1, LocalDate.of(2000, 1, 31)));
        assertEquals(LocalDate.of(2025, 4, 30), CalendarMonths.movedBy(-1, LocalDate.of(2025, 5, 31)));
    }

    /** Two moves are not the move by their sum, and two dates may land on one. */
    @Test
    void movesByMonthsDoNotAddUp() {
        LocalDate end = LocalDate.of(2025, 1, 31);
        assertEquals(LocalDate.of(2025, 3, 28),
                CalendarMonths.movedBy(1, CalendarMonths.movedBy(1, end)));
        assertEquals(LocalDate.of(2025, 3, 31), CalendarMonths.movedBy(2, end));
        assertEquals(CalendarMonths.movedBy(1, LocalDate.of(2025, 1, 30)),
                CalendarMonths.movedBy(1, end));
        assertNotEquals(CalendarMonths.movedBy(1, CalendarMonths.movedBy(1, end)),
                CalendarMonths.movedBy(2, end));
    }

    /** Past either end of the calendar there is no date, however far past. */
    @Test
    void pastTheCalendarThereIsNoDate() {
        assertNull(CalendarMonths.movedBy(1, LocalDate.MAX));
        assertNull(CalendarMonths.movedBy(-1, LocalDate.MIN));
        assertNull(CalendarMonths.movedBy(Long.MAX_VALUE, LocalDate.MIN));
        assertNull(CalendarMonths.movedBy(Long.MIN_VALUE, LocalDate.MAX));
        assertNull(CalendarMonths.movedBy(Long.MAX_VALUE, LocalDate.of(2025, 1, 1)));
        assertEquals(LocalDate.MAX.withDayOfMonth(30).minusMonths(1),
                CalendarMonths.movedBy(-1, LocalDate.MAX));
        assertEquals(LocalDate.MIN.plusMonths(1), CalendarMonths.movedBy(1, LocalDate.MIN));
    }

    /** Over dates either side of year nought, of every day a month ends on, and moves of either
     *  sign up to the calendar's whole span and past it, the date is the runtime's and the month
     *  is the one the month alone says. */
    @Test
    void everyMoveIsTheRuntimes() {
        List<LocalDate> dates = new ArrayList<>();
        for (int year : new int[] {-401, -400, -5, -4, -1, 0, 1, 1900, 2000, 2024, 2025, 2100}) {
            for (int month = 1; month <= 12; month++) {
                for (int day : new int[] {1, 15, 28, 29, 30, 31}) {
                    LocalDate first = LocalDate.of(year, month, 1);
                    dates.add(first.withDayOfMonth(Math.min(day, first.lengthOfMonth())));
                }
            }
        }
        dates.add(LocalDate.MIN);
        dates.add(LocalDate.MAX);
        long span = (LocalDate.MAX.getYear() - (long) LocalDate.MIN.getYear()) * 12 + 11;
        long[] moves = {0, 1, -1, 2, -2, 11, -11, 12, -12, 13, -13, 25, -25, 4800, -4800, span,
                -span, span + 1, -span - 1, Long.MAX_VALUE, Long.MIN_VALUE};
        for (LocalDate date : dates) {
            for (long months : moves) {
                LocalDate landed = CalendarMonths.movedBy(months, date);
                assertEquals(runtime(months, date), landed, date + " moved by " + months);
                if (landed != null) {
                    assertEquals(landed.getMonthValue(),
                            CalendarMonths.monthLandedIn(date.getMonthValue(), months),
                            date + " moved by " + months);
                }
            }
        }
    }

    /** What the runtime answers, or null where it stops. */
    private static LocalDate runtime(long months, LocalDate date) {
        try {
            return date.plusMonths(months);
        } catch (DateTimeException _) {
            return null;
        }
    }
}
