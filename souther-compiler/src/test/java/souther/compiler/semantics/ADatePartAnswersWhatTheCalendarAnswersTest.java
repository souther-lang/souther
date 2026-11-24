package souther.compiler.semantics;

import org.junit.jupiter.api.Test;

import java.time.LocalDate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A part of a date is the number the calendar gives for it, at the ends of the calendar, in a
 * year before the first, on a leap day and on the last day of a year.
 */
class ADatePartAnswersWhatTheCalendarAnswersTest {

    @Test
    void eachPartIsTheNumberTheCalendarGives() {
        List<LocalDate> dates = List.of(
                LocalDate.MIN,
                LocalDate.of(-1, 12, 31),
                LocalDate.of(0, 1, 1),
                LocalDate.of(1900, 2, 28),
                LocalDate.of(2000, 2, 29),
                LocalDate.of(2023, 12, 31),
                LocalDate.MAX);
        for (LocalDate date : dates) {
            assertEquals(date.getYear(), TakenAs.DatePart.YEAR.of(date), "year of " + date);
            assertEquals(date.getMonthValue(), TakenAs.DatePart.MONTH.of(date), "month of " + date);
            assertEquals(date.getDayOfMonth(), TakenAs.DatePart.DAY.of(date), "day of " + date);
        }
    }
}
