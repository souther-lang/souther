package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.Type;

import java.time.Instant;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.LocalTime;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Building a temporal from parts a model already holds (issue #623).
 *
 * <p>The issue reported that there was no way in. There was: a written anchor and three additions
 * reach any date, because the arithmetic takes arbitrary Ints. What that route has no way to do is
 * refuse — {@code Date("0001-01-01") |> addYears(2025) |> addMonths(1) |> addDays(29)} answers the
 * 2nd of March for a model that asked for the 30th of February, and nothing downstream can tell that
 * from the day it asked for. So what is added here is not an entrance but a refusal: {@code
 * fromParts} reads the parts as a day and says when they name none.
 *
 * <p>The law that makes it the way back rather than a second way in is that it inverts the readers.
 * Held here against dates the readers were taken from, so the two cannot drift apart into agreeing
 * about a spelling while disagreeing about a value.
 */
class ATemporalIsBuiltFromThePartsAModelHoldsTest {

    /** Every date this walks the law over: a leap day, a month end, the first, and the far ends. */
    private static final List<String> DATES = List.of(
            "2026-07-26", "2024-02-29", "2026-02-28", "2026-01-01", "2026-12-31",
            "0001-01-01", "+999999999-12-31", "-999999999-01-01");

    private static final List<String> TIMES = List.of(
            "00:00", "09:30", "23:59:59", "12:00:01");

    @Test
    void fromPartsInvertsTheReadersOverEveryDate() throws Exception {
        BytesClassLoader loader = compile("""
                module demo

                data In = { on: Date }
                data Out = { same: Bool }

                behavior roundTrip : (i: In) -> Out constructs Out

                let roundTrip (i) =
                    match Date.fromParts(Date.year(i.on), Date.month(i.on), Date.day(i.on)) with
                    | Date as back -> Out { same = back == i.on }
                    | NotADate -> Out { same = false }
                """);
        for (String iso : DATES) {
            assertEquals(true, run(loader, Emitted.impl("demo", "roundTrip"), "demo.In", "demo.Out",
                            Map.of("on", LocalDate.parse(iso))).get("same"),
                    "Date.fromParts must answer the date its parts were read from: " + iso);
        }
    }

    @Test
    void fromPartsInvertsTheReadersOverEveryTime() throws Exception {
        BytesClassLoader loader = compile("""
                module demo

                data In = { at: Time }
                data Out = { same: Bool }

                behavior roundTrip : (i: In) -> Out constructs Out

                let roundTrip (i) =
                    match Time.fromParts(Time.hour(i.at), Time.minute(i.at), Time.second(i.at)) with
                    | Time as back -> Out { same = back == i.at }
                    | NotATime -> Out { same = false }
                """);
        for (String iso : TIMES) {
            assertEquals(true, run(loader, Emitted.impl("demo", "roundTrip"), "demo.In", "demo.Out",
                            Map.of("at", LocalTime.parse(iso))).get("same"),
                    "Time.fromParts must answer the time its parts were read from: " + iso);
        }
    }

    /**
     * The refusal the anchor-and-arithmetic route could not make. Each of these reaches a real date
     * through the arithmetic — the 30th of February becomes the 2nd of March — and a case here.
     */
    @Test
    void partsThatNameNoDayTakeTheNotADateArm() throws Exception {
        BytesClassLoader loader = compile("""
                module demo

                data In = { y: Int, m: Int, d: Int }
                data Out = { named: Bool }

                behavior build : (i: In) -> Out constructs Out

                let build (i) =
                    match Date.fromParts(i.y, i.m, i.d) with
                    | Date -> Out { named = true }
                    | NotADate -> Out { named = false }
                """);
        assertEquals(true, built(loader, 2026, 7, 1));
        assertEquals(true, built(loader, 2024, 2, 29), "2024 is a leap year");
        assertEquals(false, built(loader, 2026, 2, 30), "February has no 30th");
        assertEquals(false, built(loader, 2026, 2, 29), "2026 is not a leap year");
        assertEquals(false, built(loader, 2026, 13, 1), "there is no 13th month");
        assertEquals(false, built(loader, 2026, 0, 1), "there is no month 0");
        assertEquals(false, built(loader, 2026, 1, 0), "there is no day 0");
        // a year past what a date holds is the same case: what a caller does about either is that
        // the parts it had do not name a date
        assertEquals(false, built(loader, 10_000_000_000L, 1, 1), "beyond the range a Date holds");
        assertEquals(false, built(loader, Long.MAX_VALUE, 1, 1), "past what an int can even carry");
    }

    @Test
    void partsThatNameNoTimeOfDayTakeTheNotATimeArm() throws Exception {
        BytesClassLoader loader = compile("""
                module demo

                data In = { h: Int, mi: Int, s: Int }
                data Out = { named: Bool }

                behavior build : (i: In) -> Out constructs Out

                let build (i) =
                    match Time.fromParts(i.h, i.mi, i.s) with
                    | Time -> Out { named = true }
                    | NotATime -> Out { named = false }
                """);
        assertEquals(true, timeBuilt(loader, 0, 0, 0));
        assertEquals(true, timeBuilt(loader, 23, 59, 59));
        assertEquals(false, timeBuilt(loader, 24, 0, 0), "there is no 24th hour");
        assertEquals(false, timeBuilt(loader, 12, 60, 0), "there is no 60th minute");
        assertEquals(false, timeBuilt(loader, 23, 59, 60), "the leap second is not a time of day");
        assertEquals(false, timeBuilt(loader, 0 - 1, 0, 0), "there is no hour before the first");
    }

    /** {@code fromParts} normalises nothing, which is the whole of what it adds over the arithmetic
     *  that reaches the same dates. Held against the arithmetic itself, so the difference is stated
     *  rather than assumed: the same three numbers, one route answering a date and the other a case. */
    @Test
    void whatTheArithmeticNormalisesFromPartsRefuses() throws Exception {
        BytesClassLoader loader = compile("""
                module demo

                data In = { y: Int, m: Int, d: Int }
                data Out = { byArithmetic: Date, byParts: Bool }

                behavior both : (i: In) -> Out constructs Out

                let anchored (y: Int, m: Int, d: Int): Date =
                    Date("0001-01-01")
                        |> Date.addYears(y - 1)
                        |> Date.addMonths(m - 1)
                        |> Date.addDays(d - 1)

                let both (i) =
                    match Date.fromParts(i.y, i.m, i.d) with
                    | Date -> Out { byArithmetic = anchored(i.y, i.m, i.d), byParts = true }
                    | NotADate -> Out { byArithmetic = anchored(i.y, i.m, i.d), byParts = false }
                """);
        Map<?, ?> out = run(loader, Emitted.impl("demo", "both"), "demo.In", "demo.Out",
                Map.of("y", 2026L, "m", 2L, "d", 30L));
        assertEquals(LocalDate.parse("2026-03-02").toString(), String.valueOf(out.get("byArithmetic")),
                "the arithmetic still normalises — that is what it is for");
        assertEquals(false, out.get("byParts"),
                "asked as parts, the same three numbers name no day and are told so");
    }

    /** A {@code DateTime} is a {@code Date} and a {@code Time}, and joining them cannot fail. */
    @Test
    void aDateTimeComesApartIntoADateAndATimeAndBackAgain() throws Exception {
        BytesClassLoader loader = compile("""
                module demo

                data In = { at: DateTime }
                data Out = { same: Bool, sameDate: Bool, sameTime: Bool }

                behavior split : (i: In) -> Out constructs Out

                let split (i) = {
                    let d = DateTime.toDate(i.at)
                    let t = DateTime.toTime(i.at)
                    let back = DateTime.fromDateAndTime(d, t)
                    Out { same = back == i.at
                        , sameDate = DateTime.toDate(back) == d
                        , sameTime = DateTime.toTime(back) == t
                        }
                }
                """);
        for (String iso : List.of("2026-07-26T09:30", "2026-07-26T00:00", "2026-12-31T23:59:59")) {
            Map<?, ?> out = run(loader, Emitted.impl("demo", "split"), "demo.In", "demo.Out",
                    Map.of("at", LocalDateTime.parse(iso)));
            assertEquals(true, out.get("same"), iso);
            assertEquals(true, out.get("sameDate"), iso);
            assertEquals(true, out.get("sameTime"), iso);
        }
    }

    /**
     * {@code Instant} carries what a timestamp said and offers nothing to take it apart with. Held
     * as a refusal rather than as an absence from a list: naming a part of one needs a zone, so a
     * call that asks for one is not a member this library has.
     */
    @Test
    void anInstantHasNoOperationsToReachAPartWith() {
        for (String call : List.of("Instant.year(i.at)", "Instant.toDateTime(i.at)",
                "Instant.fromParts(2026, 1, 1)", "Instant.hour(i.at)")) {
            CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                    module demo

                    data In = { at: Instant }
                    data Out = { n: Int }

                    behavior read : (i: In) -> Out constructs Out

                    let read (i) = Out { n = 1 }
                    """.replace("Out { n = 1 }", "Out { n = " + call + " }")),
                    "`" + call + "` must not be a member the library has");
            assertTrue(e.getMessage().contains("Instant"), e.getMessage());
        }
    }

    /** What an {@code Instant} does have: it is held, compared, and handed to a behavior with no
     *  implementation, which is where the zone lives. */
    @Test
    void anInstantIsHeldComparedAndHandedOut() throws Exception {
        BytesClassLoader loader = compile("""
                module demo

                data In = { a: Instant, b: Instant }
                data Out = { aFirst: Bool, keyed: Map<Instant, Int> }

                behavior order : (i: In) -> Out constructs Out

                let order (i) = Out { aFirst = i.a < i.b, keyed = Map.singleton(i.a, 1) }
                """);
        Map<?, ?> out = run(loader, Emitted.impl("demo", "order"), "demo.In", "demo.Out",
                Map.of("a", Instant.parse("2026-01-01T00:00:00Z"),
                        "b", Instant.parse("2026-01-01T00:00:00.000000001Z")));
        assertEquals(true, out.get("aFirst"), "an Instant orders to the nanosecond");
        assertEquals(Map.of("2026-01-01T00:00:00Z", 1L), out.get("keyed"),
                "an Instant keys a Map by its ISO form");
    }

    /**
     * The new failure cases are written in a {@code match} arm and nowhere else, which is what
     * {@code NotANumber} and {@code DivisionByZero} already are. Pinned because the two directions
     * read alike in a signature — a {@code let} may *answer* {@code Date | NotADate}, and the value
     * it answers with has to have come from {@code fromParts} rather than been written.
     */
    @Test
    void aRuntimeFailureCaseIsMatchedRatherThanWritten() {
        for (String name : List.of("NotADate", "NotATime")) {
            CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                    module demo

                    data In = { y: Int }
                    data Out = { n: Int }

                    let pass (y: Int): Date | %s =
                        match Date.fromParts(y, 1, 1) with
                            | Date as d -> d
                            | %s -> %s

                    behavior go : (i: In) -> Out constructs Out

                    let go (i) = Out { n = i.y }
                    """.formatted(name, name, name)),
                    "`" + name + "` must not be writable as a value");
            assertTrue(e.getMessage().contains(name), e.getMessage());
        }
    }

    /** The same signature is fine when the value comes from {@code fromParts} rather than written. */
    @Test
    void aLetMayAnswerTheUnionItGotFromFromParts() {
        Compiler.compile("""
                module demo

                data In = { y: Int }
                data Out = { n: Int }

                let firstOfJanuary (y: Int): Date | NotADate = Date.fromParts(y, 1, 1)

                behavior go : (i: In) -> Out constructs Out

                let go (i) =
                    match firstOfJanuary(i.y) with
                        | Date as d -> Out { n = Date.year(d) }
                        | NotADate -> Out { n = 0 - 1 }
                """);
    }

    /**
     * Every primitive that crosses a boundary has a decoder and an encoder, walked from the enum
     * rather than from a list written here. A primitive added to the language and left out of the
     * codec would pass a test that named the ones it knew about; this one fails.
     */
    @Test
    void everyLeafScalarCrossesABoundaryAndComesBack() throws Exception {
        List<String> missing = new ArrayList<>();
        for (LeafScalar scalar : LeafScalar.values()) {
            Type.Prim prim = scalar.type();
            Object sent = sampleOf(prim);
            assertNotNull(sent, "this test has no sample value for " + prim.shown());
            BytesClassLoader loader = compile("""
                    module demo

                    data In = { v: %s }
                    data Out = { v: %s }

                    behavior pass : (i: In) -> Out constructs Out

                    let pass (i) = Out { v = i.v }
                    """.formatted(prim.shown(), prim.shown()));
            Map<?, ?> out = run(loader, Emitted.impl("demo", "pass"), "demo.In", "demo.Out", Map.of("v", sent));
            if (out.get("v") == null) {
                missing.add(prim.shown());
            }
        }
        assertEquals(List.of(), missing, "a primitive that crosses must come back");
    }

    /** The neutral value a boundary hands over for each primitive. */
    private static Object sampleOf(Type.Prim prim) {
        return switch (prim) {
            case STRING -> "x";
            case INT -> 1L;
            case BOOL -> true;
            case DECIMAL -> new java.math.BigDecimal("1.5");
            case DATE -> LocalDate.parse("2026-07-26");
            case TIME -> LocalTime.parse("09:30");
            case DATETIME -> LocalDateTime.parse("2026-07-26T09:30");
            case INSTANT -> Instant.parse("2026-07-26T09:30:00Z");
            case RAW -> null;   // not a LeafScalar, so never asked for
        };
    }

    private static boolean built(BytesClassLoader loader, long y, long m, long d) throws Exception {
        return (Boolean) run(loader, Emitted.impl("demo", "build"), "demo.In", "demo.Out",
                Map.of("y", y, "m", m, "d", d)).get("named");
    }

    private static boolean timeBuilt(BytesClassLoader loader, long h, long mi, long s) throws Exception {
        return (Boolean) run(loader, Emitted.impl("demo", "build"), "demo.In", "demo.Out",
                Map.of("h", h, "mi", mi, "s", s)).get("named");
    }

    private static BytesClassLoader compile(String source) throws Exception {
        return new BytesClassLoader(Compiler.compile(source),
                ATemporalIsBuiltFromThePartsAModelHoldsTest.class.getClassLoader());
    }

    private static Map<?, ?> run(BytesClassLoader loader, String impl, String in, String out,
                                 Map<String, Object> input) throws Exception {
        Object decoded = Codecs.decoded(loader, in, input);
        Object answered = Codecs.apply(
                loader.loadClass(impl).getConstructor().newInstance(), decoded);
        return assertInstanceOf(Map.class, Codecs.encode(loader, out, answered));
    }
}
