package souther.compiler.numeric;

import java.time.LocalDate;
import java.time.Year;
import java.time.YearMonth;

/**
 * Where a date lands moved by whole calendar months, as the library's move by months answers it.
 *
 * <p>The months are counted from the first month of year nought, so a date in month {@code m} of
 * year {@code y} stands at {@code 12y + m - 1}. Moved by {@code k} months it lands in the month
 * that count plus {@code k} stands at: the year is the count floored by twelve, and the month is
 * what the count leaves by twelve, plus one. Floored and not truncated, since the years before
 * nought are dates as well. The day is the date's own, or the last day of the month it lands in
 * where that month is shorter. And where the month it lands in is past the calendar's first or
 * last year, there is no date to land on and the run stops.
 *
 * <p>No move by days. How many days a month moves a date by turns on the date, and two dates a
 * month apart may land on one: the thirtieth and the thirty-first of January both land on the last
 * day of February. So a move by months is not one by any count of days, and two moves are not the
 * move by their sum — a month after a month after the thirty-first of January is the
 * twenty-eighth of March, and two months after it is the thirty-first.
 *
 * <p>The one place this is worked out. A reader that asks which month a moved date lands in reads
 * it as {@link #monthLandedIn} says, so the two cannot disagree.
 */
public final class CalendarMonths {

    /** How many months a year has, which is the divisor the month a move lands in is left by. */
    public static final int A_YEAR = 12;

    /** The number the first month of a year is counted as. */
    public static final int FIRST = 1;

    private CalendarMonths() {
    }

    /**
     * The date {@code months} calendar months on from {@code date}, or null where the month it
     * lands in is past the calendar.
     *
     * <p>The count is worked out exactly: a number of months the count cannot hold is more than
     * the calendar's years are months, and lands past it.
     */
    public static LocalDate movedBy(long months, LocalDate date) {
        long landed;
        try {
            landed = Math.addExact(monthsFromYearNought(date), months);
        } catch (ArithmeticException _) {
            return null;
        }
        long year = Math.floorDiv(landed, A_YEAR);
        if (year < Year.MIN_VALUE || year > Year.MAX_VALUE) {
            return null;
        }
        YearMonth month = YearMonth.of((int) year, Math.floorMod(landed, A_YEAR) + FIRST);
        return month.atDay(Math.min(date.getDayOfMonth(), month.lengthOfMonth()));
    }

    /**
     * The month a date in month {@code month} lands in moved by {@code months}: what
     * {@code month - 1 + months} leaves by twelve, plus one.
     *
     * <p>Whatever the date's year and day are, and wherever the move lands: where it lands past
     * the calendar there is no date, and this is the month there would be.
     */
    public static int monthLandedIn(int month, long months) {
        return Math.floorMod(month - FIRST + Math.floorMod(months, A_YEAR), A_YEAR) + FIRST;
    }

    /** The months from the first month of year nought to the one {@code date} falls in. */
    private static long monthsFromYearNought(LocalDate date) {
        return date.getYear() * (long) A_YEAR + date.getMonthValue() - FIRST;
    }
}
