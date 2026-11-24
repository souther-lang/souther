package souther.compiler.numeric;

import java.time.LocalDate;

/**
 * The day rows are written on, which is where a date nothing fixes is looked for first.
 *
 * <p>A preference and never a bound. Which dates a rule leaves is read from the source alone; this
 * says only which of them a search tries first, so a row written on one day fills its point on any
 * other.
 *
 * @param date the day itself
 */
public record Today(LocalDate date) {

    public Today {
        if (date == null) {
            throw new IllegalArgumentException("today is a day");
        }
    }

    /** Today, as the count a date's order runs on. */
    public Count day() {
        return Dates.dayOf(date);
    }

    /** The year today is in. */
    public int year() {
        return date.getYear();
    }

    /** The first day of the year today is in, as a count of days. */
    public long firstOfItsYear() {
        return date.withDayOfYear(1).toEpochDay();
    }
}
