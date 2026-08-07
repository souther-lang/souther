package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Three separate implementations answer "read a value of type T from the outside": the derived codec
 * a data field crosses through, the fixture builder an {@code example} uses, and
 * {@code Runner.decoderFor} behind {@code souther run}. They are written independently, so they drift
 * — issue #97 was exactly that, a collection argument the boundary read and the fixture builder did
 * not.
 *
 * <p>This pins what each supports against the same table of types, so adding a capability to one
 * without the others fails here rather than in whatever example happens to use it. A row states that
 * all three read the type; a row stating that one of them does not would fix a gap in place, and a
 * test that holds a gap open is worse than the gap.
 *
 * <p>What a boundary admits is not this table's to decide. The types below are the ones the checker
 * lets cross, so a row is a claim about the three readers rather than about the boundary — see
 * {@code TypeOps} for the rule and {@link EncoderPathAgreementTest} for the writing side.
 */
class DecoderPathAgreementTest {

    @TempDir
    Path dir;

    // === what all three read ===

    @Test
    void aPrimitiveIsReadByAllThree() throws Exception {
        acceptedEverywhere("Int", 3L, "3", 3L);
    }

    @Test
    void aNewtypeIsReadByAllThree() throws Exception {
        // declared as `data Wrapped = Int` in the modules below
        acceptedEverywhere("Wrapped", 3L, "3", 3L);
    }

    @Test
    void aListIsReadByAllThree() throws Exception {
        acceptedEverywhere("List<Int>", List.of(1L, 2L), "[1, 2]", 2L);
    }

    @Test
    void aStringKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<String, Int>", Map.of("a", 1L), "{\"a\": 1}", 1L);
    }

    /**
     * A temporal was missing from this table, and that gap is how issue #119 shipped: `run` parsed
     * JSON and decoded it with the neutral-source decoders, so a Date could not be passed to it at
     * all — as a parameter or inside a data — while the boundary and a fixture both read one.
     */
    @Test
    void aDateIsReadByAllThree() throws Exception {
        acceptedEverywhere("Date", LocalDate.parse("2026-01-31"), "\"2026-01-31\"", 31L);
    }

    @Test
    void aDateTimeIsReadByAllThree() throws Exception {
        acceptedEverywhere("DateTime", LocalDateTime.parse("2026-01-31T09:00"),
                "\"2026-01-31T09:00\"", 31L);
    }

    @Test
    void aListOfDatesIsReadByAllThree() throws Exception {
        acceptedEverywhere("List<Date>", List.of(LocalDate.parse("2026-01-01")),
                "[\"2026-01-01\"]", 1L);
    }

    /**
     * A boundary map is keyed by a {@code String}, a String-backed newtype, {@code Date},
     * {@code DateTime} or an enumeration, and all three readers read all five. The rows are written
     * out one kind at a time because the key is where a reader composing its own decoder is most
     * likely to admit fewer kinds than the boundary does.
     */
    @Test
    void aNewtypeKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<Key, Int>", Map.of("a", 1L), "{\"a\": 1}", 1L);
    }

    @Test
    void aDateKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<Date, Int>", Map.of("2026-01-01", 1L), "{\"2026-01-01\": 1}", 1L);
    }

    @Test
    void aDateTimeKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<DateTime, Int>", Map.of("2026-01-01T09:00", 1L),
                "{\"2026-01-01T09:00\": 1}", 1L);
    }

    @Test
    void anEnumerationKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<Outcome, Int>", Map.of("Won", 1L), "{\"Won\": 1}", 1L);
    }

    /**
     * A {@code String} key arrives canonical, like every other text a boundary reads. The keys of a
     * decoded object do not pass the string leaf on their way in, so a reader that leaves them where
     * they landed hands the domain the one text it never made canonical — and a lookup written the
     * other way misses a key that is there.
     */
    @Test
    void aStringKeyIsCanonicalWhicheverWayItWasWritten() throws Exception {
        String composed = "\u304c";              // one code point
        String decomposed = "\u304b\u3099";      // the base and the combining mark, the same text
        Path file = dir.resolve("key.sou");
        Files.writeString(file, """
                module demo
                behavior at : (m: Map<String, Int>) -> Int
                let at (m) = Option.withDefault(0, Map.get("%s", m))
                """.formatted(composed));
        assertEquals("7", Runner.run(file, "at", "{\"" + decomposed + "\": 7}").trim(),
                "the key the module looks up is the key the input carried");
    }

    /** A key the key type refuses is refused at that key's own path, and every key is read before
     *  the map is given up on, so a map with two bad keys is answered about both at once. */
    @Test
    void aBadKeyIsRefusedWhereItStands() {
        Runner.RunException refused = assertThrows(Runner.RunException.class,
                () -> runReads("Map<Bounded, Int>", "{\"ab\": 1, \"cd\": 2}"));
        assertTrue(refused.getMessage().contains("/ab"), refused.getMessage());
        assertTrue(refused.getMessage().contains("/cd"), refused.getMessage());
    }

    // === the three paths ===

    private void acceptedEverywhere(String type, Object neutral, String runJson, Object size)
            throws Exception {
        assertTrue(boundaryReads(type, neutral), "the derived codec reads " + type);
        assertTrue(fixtureReads(type, fixtureOf(type), size), "a fixture writes " + type);
        assertEquals(String.valueOf(size), runReads(type, runJson).trim(), "run reads " + type);
    }

    private static String fixtureOf(String type) {
        return switch (type) {
            case "Int" -> "3";
            case "Wrapped" -> "Wrapped(3)";
            case "List<Int>" -> "[ 1, 2 ]";
            case "Map<String, Int>" -> "[ (\"a\", 1) ]";
            case "Date" -> "Date(\"2026-01-31\")";
            case "DateTime" -> "DateTime(\"2026-01-31T09:00\")";
            case "List<Date>" -> "[ Date(\"2026-01-01\") ]";
            case "Map<Key, Int>" -> "[ (Key(\"a\"), 1) ]";
            case "Map<Date, Int>" -> "[ (Date(\"2026-01-01\"), 1) ]";
            case "Map<DateTime, Int>" -> "[ (DateTime(\"2026-01-01T09:00\"), 1) ]";
            case "Map<Outcome, Int>" -> "[ (Won, 1) ]";
            default -> throw new IllegalArgumentException(type);
        };
    }

    /** The types the rows are written in, declared the same way for all three paths — each path
     *  reads the same module but for the one line that puts the type in position. */
    private static final String DECLS = """
            data Key = String
            data Wrapped = Int
            data Outcome = Won | Lost
            data Bounded = String
                invariant longEnough = String.length(value) >= 3
            """;

    /** A data with a field of that type, decoded through its generated codec. */
    private boolean boundaryReads(String type, Object neutral) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo
                %s
                data Holder = { v: %s }
                """.formatted(DECLS, type)), getClass().getClassLoader());
        Object decoded = Codecs.decode(loader, "demo.Holder", Map.of("v", neutral));
        return "Ok".equals(decoded.getClass().getSimpleName());
    }

    /** A behavior taking that type, with an `example` whose fixture writes it. The compile evaluates
     *  the example, so a fixture the builder cannot construct fails the compile. */
    private boolean fixtureReads(String type, String fixture, Object expected) {
        Compiler.compile("""
                module demo
                %s
                data Out = { n: Int }
                behavior take : (v: %s) -> Out constructs Out
                let take (v) = Out { n = %s }
                example take
                  | "reads it" : (%s) -> Out { n = %s }
                """.formatted(DECLS, type, sizeExprFor(type), fixture, expected));
        return true;
    }

    /** The same type as a behavior input, driven through {@code souther run}. */
    private String runReads(String type, String json) throws Exception {
        Path file = dir.resolve("run" + Math.abs(type.hashCode()) + ".sou");
        Files.writeString(file, """
                module demo
                %s
                behavior take : (v: %s) -> Int
                let take (v) = %s
                """.formatted(DECLS, type, sizeExprFor(type)));
        return Runner.run(file, "take", json);
    }

    /** An expression reducing a value of that type to the Int the three paths compare. */
    private static String sizeExprFor(String type) {
        if (type.startsWith("Map<")) {
            return "Map.size(v)";
        }
        if (type.startsWith("List<")) {
            return "List.length(v)";
        }
        return switch (type) {
            case "Wrapped" -> "v.value";
            case "Date" -> "Date.day(v)";
            case "DateTime" -> "Date.day(DateTime.toDate(v))";
            default -> "v";
        };
    }
}
