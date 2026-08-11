package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.msg.TypeMessage;

import org.junit.jupiter.api.io.TempDir;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a temporal holds is the type's rule and not the decoder path's.
 *
 * <p>The refinements were emitted where a field's leaf was built, and a map key spelled its own
 * parse beside it — so a `Time` under a key admitted `09:00:00.5`, which the same `Time` at a field
 * refused. A rule that changes with the way in is not the type's rule, and the value that got
 * through is one nothing downstream can tell from the value that was sent.
 *
 * <p>Walked over both paths for both refusals rather than sampled. The all-primitives round-trip in
 * {@link ATemporalIsBuiltFromThePartsAModelHoldsTest} goes through fields only, which is exactly why
 * it did not catch this.
 *
 * <p>The paths walked are the ones this compiler builds the parse for: a JSON field, a map key from
 * every source, and the runner's own decoders, which read a top-level argument and were a third
 * copy of the policy until they were made to read the one table ({@code TemporalRule}).
 *
 * <p>One path is not covered and is not a decision: the bare-value factory is Raoh's own and parses
 * text inside itself, where nothing here can stand. A leap second handed to it as text still reaches
 * the moment before it, against the rule the specification states, so
 * {@link #aLeapSecondIsRefusedAtTheNeutralDecoderToo} is written as the rule and disabled rather
 * than written as the behaviour and passing.
 */
class ATemporalHoldsTheSameRuleAtEveryPathTest {

    private static final String AT_A_FIELD = """
            module demo

            data In = { t: Time, dt: DateTime, at: Instant }
            data Out = { n: Int }

            behavior pass : (i: In) -> Out constructs Out
            let pass (i) = Out { n = Time.hour(i.t) }
            """;

    private static final String UNDER_A_KEY = """
            module demo

            data In = { t: Map<Time, Int>, dt: Map<DateTime, Int>, at: Map<Instant, Int> }
            data Out = { n: Int }

            behavior pass : (i: In) -> Out constructs Out
            let pass (i) = Out { n = Map.size(i.t) }
            """;

    /** A fraction of a second is refused at a field and under a key alike. */
    @Test
    void aTimeOfDayIsHeldToTheSecondWhereverItArrives() throws Exception {
        for (String[] field : new String[][] {{"t", "09:00:00.5"}, {"dt", "2026-07-01T09:00:00.123"}}) {
            assertRefused(AT_A_FIELD, field[0], field[1], "holds no fraction of a second");
            assertRefusedKey(field[0], field[1], "holds no fraction of a second");
        }
    }

    /** So is a leap second, which `Instant.parse` would otherwise answer as the second before. */
    @Test
    void aLeapSecondIsRefusedWhereverItArrives() throws Exception {
        assertRefusedJson(AT_A_FIELD, "at", "2026-06-30T23:59:60Z", "names a leap second");
        assertRefusedKey("at", "2026-06-30T23:59:60Z", "names a leap second");
    }

    /**
     * The one path where it is not refused, written as the rule says it should be and disabled.
     *
     * <p>A leap second handed to the bare-value decoder as text still reaches the moment before it.
     * The parse is inside {@code ObjectDecoders.iso8601()}, which takes a real {@code Instant} as
     * itself and parses a {@code String} with {@code Instant::parse}; Raoh has no combinator that
     * lets the text be refined before that, and nothing on this side can stand between them.
     *
     * <p>Written as an assertion of the rule rather than of the behaviour, and disabled, because the
     * rule is what the specification says
     * (<<a-leap-second-is-no-moment>>: refused where it is written <em>and where it arrives</em>) and
     * a test asserting the other thing would make a violation look like a decision. It turns green
     * when Raoh refuses a leap second, which is where the fix belongs: an {@code iso8601()} that
     * answers an {@code Instant} after losing the fact that the text named a second it does not have
     * is answering about a different moment.
     */
    @Test
    @org.junit.jupiter.api.Disabled("needs a Raoh that refuses a leap second, or one that lets the "
            + "text be refined before it parses — see the note on this method")
    void aLeapSecondIsRefusedAtTheNeutralDecoderToo() throws Exception {
        net.unit8.raoh.Result<?> r = decoded(AT_A_FIELD, fieldsWith("at", "2026-06-30T23:59:60Z"));
        assertTrue(!r.isOk(), "a leap second must not be admitted at a bare-value field");
        assertTrue(String.valueOf(r).contains("names a leap second"), String.valueOf(r));
    }

    /** And what each path still takes, so the refusals are not a boundary that stopped working. */
    @Test
    void whatEachPathStillTakes() throws Exception {
        assertTrue(decoded(AT_A_FIELD, fieldsWith("t", "09:00:00")).isOk());
        assertTrue(decoded(AT_A_FIELD, fieldsWith("at", "2026-07-01T09:00:00Z")).isOk());
        assertTrue(decoded(UNDER_A_KEY, keysWith("t", "09:00:00")).isOk());
        assertTrue(decoded(UNDER_A_KEY, keysWith("at", "2026-07-01T09:00:00Z")).isOk());
    }

    /**
     * An offset is taken at a boundary and refused in source, and the two are not in tension.
     *
     * <p>{@code 09:30+09:00} and {@code 00:30Z} are one moment, so nothing is lost by reading either
     * — which is why the boundary reads both. A written value is written the way the value is
     * written back, and an {@code Instant} is written in UTC, which is why source takes one.
     */
    @Test
    void anOffsetCrossesTheBoundaryAndIsNotWrittenInSource() throws Exception {
        assertTrue(decoded(AT_A_FIELD, fieldsWith("at", "2026-07-01T09:00:00+09:00")).isOk(),
                "an offset names the same moment, so the boundary takes it");
        assertTrue(decoded(UNDER_A_KEY, keysWith("at", "2026-07-01T09:00:00+09:00")).isOk());

        CompileException written = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Out = { at: Instant }

                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { at = Instant("2026-07-01T09:00:00+09:00") }
                """));
        assertInstanceOf(TypeMessage.AnInstantIsWrittenInUtc.class, written.diagnostic().said(),
                written.getMessage());
    }

    /** A written leap second is refused where it is written, as it is where it arrives. */
    @Test
    void aWrittenLeapSecondIsRefusedToo() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Out = { at: Instant }

                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { at = Instant("2026-06-30T23:59:60Z") }
                """));
        assertInstanceOf(TypeMessage.ALeapSecondIsNotAMoment.class, e.diagnostic().said(),
                e.getMessage());
    }

    private static void assertRefused(String model, String field, String text, String says)
            throws Exception {
        net.unit8.raoh.Result<?> r = decoded(model, fieldsWith(field, text));
        assertTrue(!r.isOk(), field + "=" + text + " must not be admitted at a field");
        assertTrue(String.valueOf(r).contains(says), "at a field: " + r);
        assertRefusedJson(model, field, text, says);
    }

    /** The JSON path, where this compiler builds the parse out of Raoh's string leaf. */
    private static void assertRefusedJson(String model, String field, String text, String says)
            throws Exception {
        BytesClassLoader loader = load(model);
        JsonNode node = MAPPER.valueToTree(fieldsWith(field, text));
        net.unit8.raoh.Result<?> r = Codecs.decode(loader, "demo.In", "jsonDecoder", node);
        assertTrue(!r.isOk(), field + "=" + text + " must not be admitted at a JSON field");
        assertTrue(String.valueOf(r).contains(says), "at a JSON field: " + r);
    }

    private static void assertRefusedKey(String field, String text, String says) throws Exception {
        net.unit8.raoh.Result<?> r = decoded(UNDER_A_KEY, keysWith(field, text));
        assertTrue(!r.isOk(), field + "=" + text + " must not be admitted under a key");
        assertTrue(String.valueOf(r).contains(says), "under a key: " + r);
    }

    /** Every field filled with something the type takes, then the one under test replaced. */
    private static Map<String, Object> fieldsWith(String field, String text) {
        return replaced(Map.of("t", "09:00:00", "dt", "2026-07-01T09:00:00",
                "at", "2026-07-01T09:00:00Z"), field, text);
    }

    private static Map<String, Object> keysWith(String field, String text) {
        Map<String, Object> raw = fieldsWith(field, text);
        return Map.of("t", Map.of(raw.get("t"), 1L), "dt", Map.of(raw.get("dt"), 1L),
                "at", Map.of(raw.get("at"), 1L));
    }

    private static Map<String, Object> replaced(Map<String, Object> base, String key, Object value) {
        return base.keySet().stream().collect(java.util.stream.Collectors.toMap(
                k -> k, k -> k.equals(key) ? value : base.get(k)));
    }

    /**
     * {@code souther run}, whose decoders are built in Java rather than emitted.
     *
     * <p>A top-level argument does not go through a data's generated decoder, so this is where the
     * rules went missing next: a bare {@code Time} took {@code 09:00:00.5} and a bare {@code Instant}
     * took a leap second, both refused a field away. Walked over a bare position and a top-level map
     * for each, because those are the two shapes the runner builds a decoder for.
     */
    @Test
    void theRunnerReadsATopLevelArgumentUnderTheSameRules() throws Exception {
        Path file = dir.resolve("toplevel.sou");
        Files.writeString(file, """
                module demo

                data Out = { n: Int }

                behavior atATime : (t: Time) -> Out constructs Out
                let atATime (t) = Out { n = Time.hour(t) }

                behavior atAMoment : (dt: DateTime) -> Out constructs Out
                let atAMoment (dt) = Out { n = 1 }

                behavior atAnInstant : (at: Instant) -> Out constructs Out
                let atAnInstant (at) = Out { n = 1 }

                behavior keyedByTime : (m: Map<Time, Int>) -> Out constructs Out
                let keyedByTime (m) = Out { n = Map.size(m) }
                """);

        for (String[] refused : new String[][] {
                {"atATime", "\"09:00:00.5\"", "holds no fraction of a second"},
                {"atAMoment", "\"2026-07-01T09:00:00.123\"", "holds no fraction of a second"},
                {"atAnInstant", "\"2026-06-30T23:59:60Z\"", "names a leap second"},
                {"keyedByTime", "{\"09:00:00.5\": 1}", "holds no fraction of a second"}}) {
            Exception e = assertThrows(Exception.class,
                    () -> Runner.run(file, refused[0], refused[1]),
                    refused[0] + " must not take " + refused[1]);
            assertTrue(String.valueOf(e.getMessage()).contains(refused[2]),
                    refused[0] + ": " + e.getMessage());
        }

        for (String[] taken : new String[][] {
                {"atATime", "\"09:00:00\""},
                {"atAMoment", "\"2026-07-01T09:00:00\""},
                {"atAnInstant", "\"2026-07-01T09:00:00Z\""},
                {"keyedByTime", "{\"09:00:00\": 1}"}}) {
            assertTrue(Runner.run(file, taken[0], taken[1]).contains("\"n\""),
                    taken[0] + " must still take " + taken[1]);
        }
    }

    @TempDir
    Path dir;

    private static final JsonMapper MAPPER = JsonMapper.builder().build();

    private static BytesClassLoader load(String model) {
        return new BytesClassLoader(Compiler.compile(model),
                ATemporalHoldsTheSameRuleAtEveryPathTest.class.getClassLoader());
    }

    private static net.unit8.raoh.Result<?> decoded(String model, Map<String, Object> input)
            throws Exception {
        return Codecs.decode(load(model), "demo.In", input);
    }

}
