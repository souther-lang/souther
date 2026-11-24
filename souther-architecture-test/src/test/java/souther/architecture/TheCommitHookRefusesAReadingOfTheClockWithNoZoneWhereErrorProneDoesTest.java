package souther.architecture;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import souther.architecture.TheCommitHook.Filed;

import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.architecture.TheCommitHook.Filed.acceptedByBoth;
import static souther.architecture.TheCommitHook.Filed.hookStandsAside;
import static souther.architecture.TheCommitHook.Filed.refusedByBoth;

/**
 * What the pre-commit hook says about a reading of the clock that names no zone, held against what
 * Error Prone's JavaTimeDefaultTimeZone says of the same source.
 *
 * <p>Each case is an expression, and what Error Prone refuses in it is what it gives when it is run
 * over it ({@link TheCommitHook}). The hook may refuse less than Error Prone and never more, and
 * where it refuses less the case says so.
 */
class TheCommitHookRefusesAReadingOfTheClockWithNoZoneWhereErrorProneDoesTest {

    /** Each expression is over the clock {@code clock}. */
    private static final List<Filed> CASES = List.of(
            refusedByBoth("a date", "LocalDate.now()"),
            refusedByBoth("a date and time", "LocalDateTime.now()"),
            refusedByBoth("a time", "LocalTime.now()"),
            refusedByBoth("a day of a month", "MonthDay.now()"),
            refusedByBoth("an offset date and time", "OffsetDateTime.now()"),
            refusedByBoth("an offset time", "OffsetTime.now()"),
            refusedByBoth("a year", "Year.now()"),
            refusedByBoth("a month of a year", "YearMonth.now()"),
            refusedByBoth("a zoned date and time", "ZonedDateTime.now()"),
            refusedByBoth("the clock of the machine's zone", "Clock.systemDefaultZone()"),
            refusedByBoth("a date inside an argument", "List.of(LocalDate.now(), Year.now())"),
            hookStandsAside("a date written with its package", "java.time.LocalDate.now()"),

            acceptedByBoth("a date in the machine's zone, said", "LocalDate.now(ZoneId.systemDefault())"),
            acceptedByBoth("a date off a clock", "LocalDate.now(clock)"),
            acceptedByBoth("a clock in the machine's zone, said", "Clock.system(ZoneId.systemDefault())"),
            acceptedByBoth("the clock in UTC", "Clock.systemUTC()"),
            acceptedByBoth("a moment", "Instant.now()"),
            acceptedByBoth("the machine's zone", "ZoneId.systemDefault()"));

    @Test
    void theHookStandsToErrorProneAsEachCaseSays(@TempDir Path dir) throws Exception {
        assertEquals(List.of(), TheCommitHook.disagreements(dir, "JavaTimeDefaultTimeZone",
                "JavaTimeDefaultTimeZone", CASES, (i, expression) -> """
                        import java.time.Clock;
                        import java.time.Instant;
                        import java.time.LocalDate;
                        import java.time.LocalDateTime;
                        import java.time.LocalTime;
                        import java.time.MonthDay;
                        import java.time.OffsetDateTime;
                        import java.time.OffsetTime;
                        import java.time.Year;
                        import java.time.YearMonth;
                        import java.time.ZoneId;
                        import java.time.ZonedDateTime;
                        import java.util.List;

                        final class Fixture%d {
                            Object f(Clock clock) {
                                return %s;
                            }
                        }
                        """.formatted(i, expression)));
    }
}
