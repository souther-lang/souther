package souther.compiler.numeric;

import java.time.LocalDate;

/**
 * What a date is moved by before something is taken of it, and the dates it can be moved from.
 *
 * <p>A shift by a number of days is a partial function: the calendar has a first and a last day,
 * and a date moved past either is no date, so the program that wrote the shift stops there. A
 * chain of shifts is partial in each of its steps, and the offset alone cannot say so —
 * {@code addDays(-1, addDays(1, b))} moves nothing and is defined at one date fewer than
 * {@code b} is. So the pair is what is kept: the days the whole chain moves by, and the origin
 * days at which every step of it is defined.
 *
 * <p>Closed under {@link #thenAddDays}: whatever follows a shift is one more shift, so no chain of
 * them needs a kind of its own.
 *
 * @param offsetDays the days the chain moves a date by
 * @param first      the earliest origin day at which every step is defined
 * @param last       the latest origin day at which every step is defined
 */
public record DateTranslation(long offsetDays, long first, long last) {

    private static final long FIRST_DAY = LocalDate.MIN.toEpochDay();
    private static final long LAST_DAY = LocalDate.MAX.toEpochDay();

    /**
     * Only a chain that is defined somewhere, at dates the calendar has and that move to dates it
     * has: a translation whose first or last origin is no date, or moves to none, would say
     * {@link #definedAt} of a day no program reaches.
     */
    public DateTranslation {
        if (first > last) {
            throw new IllegalArgumentException(
                    "a translation defined at no date is not one: " + first + " > " + last);
        }
        if (!inCalendar(first) || !inCalendar(last) || !movesIntoCalendar(first, offsetDays)
                || !movesIntoCalendar(last, offsetDays)) {
            throw new IllegalArgumentException("a translation is defined at dates and moves them"
                    + " to dates: " + first + " to " + last + " moved by " + offsetDays);
        }
    }

    private static boolean inCalendar(long day) {
        return FIRST_DAY <= day && day <= LAST_DAY;
    }

    private static boolean movesIntoCalendar(long day, long by) {
        try {
            return inCalendar(Math.addExact(day, by));
        } catch (ArithmeticException _) {
            return false;
        }
    }

    /** The first date this is defined at, moved. */
    public LocalDate firstMoved() {
        return LocalDate.ofEpochDay(first + offsetDays);
    }

    /** The last date this is defined at, moved. */
    public LocalDate lastMoved() {
        return LocalDate.ofEpochDay(last + offsetDays);
    }

    /** Moving nothing, at every date there is. */
    public static DateTranslation none() {
        return new DateTranslation(0, FIRST_DAY, LAST_DAY);
    }

    /**
     * This, followed by a shift of {@code days}, or null where no date is one the whole chain is
     * defined at or where the days the chain moves by are more than a count of days holds.
     */
    public DateTranslation thenAddDays(long days) {
        try {
            long moved = Math.addExact(offsetDays, days);
            long from = Math.max(first, Math.subtractExact(FIRST_DAY, moved));
            long to = Math.min(last, Math.subtractExact(LAST_DAY, moved));
            return from > to ? null : new DateTranslation(moved, from, to);
        } catch (ArithmeticException _) {
            return null;
        }
    }

    /** Whether the chain is defined at the date {@code day} counts to. */
    public boolean definedAt(long day) {
        return first <= day && day <= last;
    }

    /** Whether this moves nothing and is defined wherever a date is. */
    public boolean isNone() {
        return equals(none());
    }

    /** Whether this is what one shift by {@link #offsetDays} is, and so says nothing a shift of
     *  that many days does not. */
    public boolean isOneShift() {
        return equals(none().thenAddDays(offsetDays));
    }

    /** The origin day a date this moves to {@code day} comes from, or null where there is none. */
    public Long originOf(long day) {
        try {
            long origin = Math.subtractExact(day, offsetDays);
            return definedAt(origin) ? origin : null;
        } catch (ArithmeticException _) {
            return null;
        }
    }

    /** How a reader of a report names the chain: the days it moves by, and where it stops being
     *  defined where that is more than the one shift says. */
    @Override
    public String toString() {
        String moved = (offsetDays >= 0 ? "+" : "") + offsetDays + " days";
        return isOneShift() ? moved
                : moved + ", defined from " + LocalDate.ofEpochDay(first) + " to "
                        + LocalDate.ofEpochDay(last);
    }
}
