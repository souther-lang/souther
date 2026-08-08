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
        return reportOn(model).lines()
                .map(String::trim)
                .filter(line -> line.startsWith("· no row is at"))
                .toList();
    }

    private static String reportOn(String model, String... extra) throws Exception {
        Path file = Files.createTempDirectory("souther-boundary").resolve("model.sou");
        Files.writeString(file, model);
        List<String> args = new java.util.ArrayList<>(List.of("examples", file.toString()));
        args.addAll(List.of(extra));
        PrintStream was = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.main(args.toArray(String[]::new));
        } finally {
            System.setOut(was);
        }
        return out.toString(StandardCharsets.UTF_8);
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

    /** An end the record moved says so. `MinuteOfDay`'s maximum is why there is an upper edge here;
     * `WorkInterval`'s clause is why it is 1439, and an author reading 1439 beside a rule that says
     * 1440 has been told half of it. */
    @Test
    void anEdgeTheRecordMovedNamesTheRecordBesideTheRuleThatPutItThere() throws Exception {
        List<String> asked = boundariesOf(TIMESHEET);

        assertTrue(asked.stream().anyMatch(l -> l.contains("interval.startsAt = 1439")
                        && l.contains("invariant MinuteOfDay (max) within WorkInterval")),
                () -> "asked for " + asked);
        assertTrue(asked.stream().anyMatch(l -> l.contains("interval.startsAt = 0")
                        && l.contains("(invariant MinuteOfDay (min))")),
                () -> "an end the record left alone names only the rule that put it there: " + asked);
    }

    /**
     * A row offered at one of these boundaries is one the decoder accepts.
     *
     * <p>The other end of the interval is chosen beside the one being fixed and not from its own
     * type: a {@code startsAt} of 1439 leaves exactly 1440 for {@code endsAt}, and taking the bottom
     * of the type's range instead is how a boundary that can be written came back as one every value
     * tried was refused at.
     */
    @Test
    void aRowIsOfferedAtEachOfThem() throws Exception {
        String report = reportOn(TIMESHEET, "--generate", "--boundaries");

        assertTrue(report.contains(
                        "startsAt = MinuteOfDay(1439), endsAt = MinuteOfDay(1440)"),
                () -> "1439 is only writable beside 1440:\n" + report);
        assertTrue(report.contains("startsAt = MinuteOfDay(0), endsAt = MinuteOfDay(1)"),
                () -> "and 0 beside anything above it:\n" + report);
        assertFalse(report.contains("every value tried was refused"),
                () -> "nothing here is out of reach:\n" + report);
    }

    /** A guard drawn at a value the record cannot hold divides nothing and is no edge either. Held
     * because the two answers are computed from one list, and a line left in the cuts while the
     * intervals dropped it is this same defect one field over. */
    @Test
    void aLineTheRecordCannotHoldIsNotABoundaryEither() throws Exception {
        String gated = TIMESHEET
                .replace("interval.endsAt.value - interval.startsAt.value >= 480",
                        "interval.startsAt.value >= 1440")
                .replace("then LongShift", "then LongShift")
                .replace("else ShortShift", "else ShortShift");
        List<String> asked = boundariesOf(gated);

        assertEquals(4, asked.size(), () -> "asked for " + asked);
        assertFalse(asked.stream().anyMatch(l -> l.contains("guard@")),
                () -> "no interval starts at 1440, so the comparison has no line to be at: " + asked);
    }

    /**
     * A row filling a class picks the rest of the record beside the value it settled on.
     *
     * <p>The boundary filler and the class filler are two searches over one record, and only one of
     * them was told what the other had fixed. A class of `720 <= x <= 1439` stands for 720, and an
     * `endsAt` taken from its own type's bottom is refused beside it.
     */
    @Test
    void aClassIsFilledBesideWhatItSettledOn() throws Exception {
        String report = reportOn(TIMESHEET.replace(
                        "interval.endsAt.value - interval.startsAt.value >= 480",
                        "interval.startsAt.value >= 720"),
                "--generate", "--boundaries");

        assertFalse(report.contains("every value tried was refused"),
                () -> "the class of the afternoon is as writable as its edge:\n" + report);
    }

    /**
     * A rule on the outer record reaches a field of a field.
     *
     * <p>The reading is of the parameter and not of each record met on the way down. Rebuilt at the
     * inner record it has never seen the outer clause, and `interval.startsAt` goes back to the top
     * of its own type — the whole of #427, one level in.
     */
    @Test
    void aRuleOnTheOuterRecordReachesAFieldOfAField() throws Exception {
        String nested = """
                module example.nested

                data Minute = Int
                    invariant withinDay = value >= 0 && value <= 1440

                data Interval =
                    { startsAt: Minute
                    , endsAt: Minute
                    }

                data Input =
                    { interval: Interval
                    , cap: Minute
                    }
                    invariant capped = interval.startsAt < cap

                data Yes
                data No

                behavior classify : (input: Input) -> Yes | No
                    constructs Yes, No

                let classify (input) = if input.interval.startsAt.value >= 100 then Yes else No

                example classify
                    | "a" : (Input { interval = Interval { startsAt = Minute(10),
                        endsAt = Minute(20) }, cap = Minute(30) }) -> No
                """;
        List<String> asked = boundariesOf(nested);

        assertTrue(asked.stream().anyMatch(l ->
                        l.contains("input.interval.startsAt = 1439")
                                && l.contains("within Input")),
                () -> "cap stops at 1440, so a start of 1440 has nothing to be under: " + asked);
        assertFalse(asked.stream().anyMatch(l -> l.contains("input.interval.startsAt = 1440")),
                () -> "asked for " + asked);
        assertFalse(reportOn(nested, "--generate", "--boundaries")
                        .contains("every value tried was refused"),
                "and each of them is a row that builds");
    }

    /**
     * An edge nothing promises is writable is reported and not counted.
     *
     * <p>Over decimals a strict rule takes nothing off either end — there is no next value to step to
     * — so both ends read `[0, 1]` while the true ranges are `[0, 1)` and `(0, 1]`. The edge is where
     * the reading stopped and not where the model does. Falling back to the type's own edge is no
     * better: the rule that could not be read refuses that value just as readily. So it is said and
     * owed to nobody, which is the account ADR-0091 already gives a combination nothing has settled.
     */
    @Test
    void anEdgeNothingPromisesIsSaidAndNotCounted() throws Exception {
        String dense = """
                module example.band

                data Ratio = Decimal
                    invariant withinOne = value >= 0.0m && value <= 1.0m

                data Band =
                    { low: Ratio
                    , high: Ratio
                    }
                    invariant ordered = low < high

                data Ok

                behavior classify : (band: Band) -> Ok
                    constructs Ok

                let classify (band) = Ok

                example classify
                    | "a" : (Band { low = Ratio(0.1m), high = Ratio(0.9m) }) -> Ok
                """;
        String report = reportOn(dense);

        assertEquals(List.of(), boundariesOf(dense), "none of them is a row anybody is owed");
        assertTrue(report.contains("boundary    0/0"), () -> report);
        assertTrue(report.contains("not known to be writable: classify/band.low = 1"), () -> report);
        assertTrue(report.contains("adequacy: satisfied"),
                () -> "and no build is refused over it:\n" + report);
    }

    /**
     * A row at the value settles what the projection could not.
     *
     * <p>A hole in a range is a rule the domain cannot keep, so neither edge of that position is
     * promised. One of them has a row sitting on it, which went through the decoder to get there —
     * reporting that value as not known to be writable is preferring an absence of argument to a
     * witness.
     */
    @Test
    void aRowAtTheValueIsTheProofTheProjectionCouldNotGive() throws Exception {
        String holed = """
                module example.holed

                data N = Int
                    invariant within = value >= 0 && value <= 10

                data R = { a: N }
                    invariant hole = a.value /= 5

                data Ok

                behavior f : (r: R) -> Ok
                    constructs Ok

                let f (r) = Ok

                example f
                    | "zero" : (R { a = N(0) }) -> Ok
                """;
        String report = reportOn(holed);

        assertTrue(report.contains("boundary    1/1"),
                () -> "the row at 0 counts, and 10 is neither met nor owed:\n" + report);
        assertFalse(report.contains("not known to be writable: f/r.a = 0"),
                () -> "there is a row at it:\n" + report);
        assertTrue(report.contains("not known to be writable: f/r.a = 10"), () -> report);
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
