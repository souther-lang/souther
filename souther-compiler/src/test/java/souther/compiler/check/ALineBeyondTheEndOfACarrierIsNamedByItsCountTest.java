package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;

import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A line a rule draws where a calendar carrier has no value is still a line, and is named.
 *
 * <p>A rule about a date shifted by a year of days draws its line a year past the last date there
 * is. Which values stand on the near side is the rule's reading; what the report writes at the line
 * is this, and a date written there would be one no model contains.
 */
class ALineBeyondTheEndOfACarrierIsNamedByItsCountTest {

    @Test
    void aDayPastTheLastDateIsNamedByItsCount() {
        long past = LocalDate.MAX.toEpochDay() + 366;

        assertEquals("day " + past, new Carrier.Days().written(Count.of(past)));
    }

    @Test
    void aDayBeforeTheFirstDateIsNamedByItsCount() {
        long before = LocalDate.MIN.toEpochDay() - 1;

        assertEquals("day " + before, new Carrier.Days().written(Count.of(before)));
    }

    @Test
    void theEndsThemselvesAreStillWrittenAsDates() {
        assertEquals("+999999999-12-31",
                new Carrier.Days().written(Count.of(LocalDate.MAX.toEpochDay())));
        assertEquals("2026-12-31",
                new Carrier.Days().written(Count.of(LocalDate.of(2026, 12, 31).toEpochDay())));
    }

    @Test
    void everyCalendarCarrierNamesAnOffRangeLineWithoutRefusing() {
        Count far = Count.of(new java.math.BigDecimal("1000000000000000000000000000000"));

        assertEquals("second " + far.spelled(), new Carrier.Seconds().written(far));
        assertEquals("second of the day " + far.spelled(), new Carrier.SecondsOfDay().written(far));
        assertEquals("nanosecond " + far.spelled(), new Carrier.Nanos().written(far));
    }
}
