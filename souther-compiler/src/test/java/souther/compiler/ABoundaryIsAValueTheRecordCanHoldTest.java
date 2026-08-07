package souther.compiler;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A boundary the report asks for is a value some row could carry.
 *
 * <p>Both ends of {@code WorkInterval} are minutes of a day, so both stop at 1440 read on their own.
 * Read where they sit, one of them cannot: a {@code startsAt} of 1440 wants an {@code endsAt} past
 * the end of the day. Asking for it is asking for a row the decoder refuses, and nothing in the
 * report tells that gap from one worth closing — which is what issue #427 reports.
 */
class ABoundaryIsAValueTheRecordCanHoldTest {

    private static final String TIMESHEET = """
            module example.timesheet

            data MinuteOfDay = Int
                invariant withinDay = value >= 0 && value <= 1440

            data WorkInterval =
                { startsAt: MinuteOfDay
                , endsAt: MinuteOfDay
                }
                invariant endsAfterStart = startsAt < endsAt

            data ShortShift
            data LongShift

            behavior classifyInterval : (interval: WorkInterval) -> ShortShift | LongShift
                constructs ShortShift, LongShift

            let classifyInterval (interval) =
                if interval.endsAt.value - interval.startsAt.value >= 480
                    then LongShift
                    else ShortShift

            example classifyInterval
                | "short" : (WorkInterval { startsAt = MinuteOfDay(540), endsAt = MinuteOfDay(600) })
                    -> ShortShift
            """;

    private static List<String> boundariesOf(String model) throws Exception {
        Path file = Files.createTempDirectory("souther-boundary").resolve("model.sou");
        Files.writeString(file, model);
        PrintStream was = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", file.toString()});
        } finally {
            System.setOut(was);
        }
        return out.toString(StandardCharsets.UTF_8).lines()
                .map(String::trim)
                .filter(line -> line.startsWith("· no row is at"))
                .toList();
    }

    @Test
    void anEdgeIsWhereTheRecordStopsAndNotWhereTheFieldsTypeDoes() throws Exception {
        List<String> asked = boundariesOf(TIMESHEET);

        assertEquals(4, asked.size(), () -> "asked for " + asked);
        assertTrue(asked.stream().anyMatch(l -> l.contains("interval.startsAt = 1439")),
                () -> "the last minute an interval can start at is 1439: " + asked);
        assertTrue(asked.stream().anyMatch(l -> l.contains("interval.endsAt = 1")),
                () -> "the first it can end at is 1: " + asked);
        assertFalse(asked.stream().anyMatch(l -> l.contains("interval.startsAt = 1440")),
                () -> "1440 would need an endsAt past the end of the day: " + asked);
        assertFalse(asked.stream().anyMatch(l -> l.contains("interval.endsAt = 0")),
                () -> "0 would need a startsAt below zero: " + asked);
    }

    /** The same two fields with the rule removed keep the whole of their type's range, so the
     * narrowing above is read as that rule doing it. */
    @Test
    void withoutTheRuleBothEndsKeepTheirTypesRange() throws Exception {
        List<String> asked = boundariesOf(TIMESHEET.replace(
                "    invariant endsAfterStart = startsAt < endsAt\n", ""));

        assertEquals(4, asked.size(), () -> "asked for " + asked);
        assertTrue(asked.stream().anyMatch(l -> l.contains("interval.startsAt = 1440")),
                () -> "nothing stops an interval starting at the end of the day now: " + asked);
        assertTrue(asked.stream().anyMatch(l -> l.contains("interval.endsAt = 0")),
                () -> "nor ending at the start of it: " + asked);
    }
}
