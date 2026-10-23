package souther.architecture;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the pre-commit hook says about a reading of the clock that names no zone, held against what
 * Error Prone's JavaTimeDefaultTimeZone says of the same source.
 *
 * <p>Each case is an expression, and the count of what Error Prone refuses in it is the count it
 * gives when it is run over it ({@link TheCommitHook}). Both counts are written down per case and
 * both are asserted, so a Checkstyle or an Error Prone that comes to answer differently fails here
 * and not in somebody's commit. The hook may refuse less than Error Prone and never more.
 */
class TheCommitHookRefusesAReadingOfTheClockWithNoZoneWhereErrorProneDoesTest {

    /** An expression, over the clock {@code clock}, and how many times each of the two refuses
     *  something in it. */
    private record Case(String name, String expression, int errorProne, int hook) {
    }

    private static Case refusedByBoth(String name, String expression) {
        return new Case(name, expression, 1, 1);
    }

    private static Case acceptedByBoth(String name, String expression) {
        return new Case(name, expression, 0, 0);
    }

    private static final List<Case> CASES = List.of(
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
            new Case("a date inside an argument", "List.of(LocalDate.now(), Year.now())", 2, 2),
            new Case("a date written with its package", "java.time.LocalDate.now()", 1, 0),

            acceptedByBoth("a date in the machine's zone, said", "LocalDate.now(ZoneId.systemDefault())"),
            acceptedByBoth("a date off a clock", "LocalDate.now(clock)"),
            acceptedByBoth("a clock in the machine's zone, said", "Clock.system(ZoneId.systemDefault())"),
            acceptedByBoth("the clock in UTC", "Clock.systemUTC()"),
            acceptedByBoth("a moment", "Instant.now()"),
            acceptedByBoth("the machine's zone", "ZoneId.systemDefault()"));

    @Test
    void whatTheHookRefusesIsNeverMoreThanErrorProneRefuses() {
        for (Case each : CASES) {
            assertTrue(each.hook() <= each.errorProne(), each.name()
                    + ": a hook that refuses more than CI stops a commit CI accepts");
        }
    }

    @Test
    void eachCaseIsRefusedAsManyTimesAsErrorProneAndTheHookEachSay(@TempDir Path dir)
            throws Exception {
        Map<Path, Case> filed = new LinkedHashMap<>();
        for (int i = 0; i < CASES.size(); i++) {
            Case each = CASES.get(i);
            Path file = dir.resolve("Fixture" + i + ".java");
            Files.writeString(file, """
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
                    """.formatted(i, each.expression()));
            filed.put(file, each);
        }
        List<Path> files = List.copyOf(filed.keySet());

        Map<Path, Integer> byErrorProne = TheCommitHook.errorProneRefusals(
                "JavaTimeDefaultTimeZone", dir, files);
        Map<Path, Integer> byTheHook = TheCommitHook.refusalsBy("JavaTimeDefaultTimeZone", files);

        List<String> disagreements = new ArrayList<>();
        for (Map.Entry<Path, Case> each : filed.entrySet()) {
            Case expected = each.getValue();
            int errorProne = byErrorProne.getOrDefault(each.getKey(), 0);
            int hook = byTheHook.getOrDefault(each.getKey(), 0);
            if (errorProne != expected.errorProne() || hook != expected.hook()) {
                disagreements.add(expected.name() + ": Error Prone refused " + errorProne
                        + " (written " + expected.errorProne() + "), the hook refused " + hook
                        + " (written " + expected.hook() + ")");
            }
        }
        assertEquals(List.of(), disagreements);
    }
}
