package souther.compiler;

import org.junit.jupiter.api.Test;

import java.time.LocalDate;
import java.time.LocalDateTime;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Three separate implementations answer "read a value of type T from the outside": the derived codec
 * a data field crosses through, the fixture builder an {@code example} uses, and
 * {@link JsonBoundary} behind {@code souther run}. They are written independently, so they drift
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
        acceptedEverywhere("Map<String, Int>", Map.of("a", 7L), "{\"a\": 7}", 7L);
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
     * A boundary map is keyed by a {@code String}, a temporal, an enumeration or a newtype over one
     * of those, and all three readers read every one. The rows are written
     * out one kind at a time because the key is where a reader composing its own decoder is most
     * likely to admit fewer kinds than the boundary does.
     */
    @Test
    void aNewtypeKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<Key, Int>", Map.of("a", 7L), "{\"a\": 7}", 7L);
    }

    @Test
    void aDateKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<Date, Int>", Map.of("2026-01-01", 7L), "{\"2026-01-01\": 7}", 7L);
    }

    @Test
    void aTimeKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<Time, Int>", Map.of("09:30:00", 7L), "{\"09:30:00\": 7}", 7L);
    }

    @Test
    void anInstantKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<Instant, Int>", Map.of("2026-01-01T09:00:00Z", 7L),
                "{\"2026-01-01T09:00:00Z\": 7}", 7L);
    }

    @Test
    void aDateTimeKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<DateTime, Int>", Map.of("2026-01-01T09:00", 7L),
                "{\"2026-01-01T09:00\": 7}", 7L);
    }

    @Test
    void anEnumerationKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<Outcome, Int>", Map.of("Won", 7L), "{\"Won\": 7}", 1L);
    }

    /** A newtype over a temporal, which is a key because its base is. The three readers reach it
     *  the way they reach any other named key — through the type's own codec — so what it wraps
     *  never has to be a kind any of them was told about. */
    @Test
    void aWrappedTemporalKeyedMapIsReadByAllThree() throws Exception {
        acceptedEverywhere("Map<Day, Int>", Map.of("2026-01-01", 7L), "{\"2026-01-01\": 7}", 7L);
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
        String source = """
                module demo
                behavior at : (m: Map<String, Int>) -> Int
                let at (m) = Option.withDefault(0, Map.get("%s", m))
                """.formatted(composed);
        assertEquals("7", Crossing.of(source, "demo", "at", "{\"" + decomposed + "\": 7}"),
                "the key the module looks up is the key the input carried");
    }

    /**
     * Two keys that are one key once decoded are refused, by the derived codec and by {@code run}
     * alike. Making a key canonical is what brings the two together, so it is also what lets an
     * object carrying both spellings arrive with a key written twice — and a map holding one entry
     * where the input wrote two is a value the input never described. Refusing where they agree is
     * as much of the contract as reading where they agree.
     *
     * <p>The fixture builder is not asked. A fixture is a list of pairs, and which of two equal keys
     * a list keeps is `Map.fromList`'s question rather than a boundary's.
     */
    @Test
    void twoKeysThatAreOneKeyOnceDecodedAreRefusedByBoth() throws Exception {
        String composed = "\u304c";
        String decomposed = "\u304b\u3099";
        java.util.Map<String, Object> both = new java.util.LinkedHashMap<>();
        both.put(composed, 1L);
        both.put(decomposed, 2L);
        assertFalse(boundaryReads("Map<String, Int>", both), "the derived codec refuses it");

        JsonBoundary.Read.Refused refused = Crossing.refusalOf(sourceTaking("Map<String, Int>"),
                "demo", "take", "{\"" + composed + "\": 1, \"" + decomposed + "\": 2}");
        List<String> said = Crossing.messagesOf(refused);
        assertTrue(said.stream().anyMatch(m -> m.contains("same key once decoded")), said.toString());
    }

    /** A key the key type refuses is refused at that key's own path, and every key is read before
     *  the map is given up on, so a map with two bad keys is answered about both at once. */
    @Test
    void aBadKeyIsRefusedWhereItStands() throws Exception {
        JsonBoundary.Read.Refused refused = Crossing.refusalOf(sourceTaking("Map<Bounded, Int>"),
                "demo", "take", "{\"ab\": 1, \"cd\": 2}");
        List<String> at = Crossing.pointersOf(refused);
        assertTrue(at.contains("/ab"), at.toString());
        assertTrue(at.contains("/cd"), at.toString());
    }

    // === the three paths ===

    private void acceptedEverywhere(String type, Object neutral, String runJson, Object answer)
            throws Exception {
        assertTrue(boundaryReads(type, neutral), "the derived codec reads " + type);
        assertTrue(fixtureReads(type, fixtureOf(type), answer), "a fixture writes " + type);
        assertEquals(String.valueOf(answer), runReads(type, runJson).trim(), "run reads " + type);
    }

    private static String fixtureOf(String type) {
        return switch (type) {
            case "Int" -> "3";
            case "Wrapped" -> "Wrapped(3)";
            case "List<Int>" -> "[ 1, 2 ]";
            case "Map<String, Int>" -> "[ (\"a\", 7) ]";
            case "Date" -> "Date(\"2026-01-31\")";
            case "DateTime" -> "DateTime(\"2026-01-31T09:00\")";
            case "List<Date>" -> "[ Date(\"2026-01-01\") ]";
            case "Map<Key, Int>" -> "[ (Key(\"a\"), 7) ]";
            case "Map<Date, Int>" -> "[ (Date(\"2026-01-01\"), 7) ]";
            case "Map<Time, Int>" -> "[ (Time(\"09:30:00\"), 7) ]";
            case "Map<Instant, Int>" -> "[ (Instant(\"2026-01-01T09:00:00Z\"), 7) ]";
            case "Map<DateTime, Int>" -> "[ (DateTime(\"2026-01-01T09:00\"), 7) ]";
            case "Map<Outcome, Int>" -> "[ (Won, 7) ]";
            case "Map<Day, Int>" -> "[ (Day(Date(\"2026-01-01\")), 7) ]";
            default -> throw new IllegalArgumentException(type);
        };
    }

    /** The types the rows are written in, declared the same way for all three paths — each path
     *  reads the same module but for the one line that puts the type in position. */
    private static final String DECLS = """
            data Key = String
            data Day = Date
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
                behavior take : (v: %s) -> Out constructs Out%s
                let take (v) = Out { n = %s }
                example take
                  | "reads it" : (%s) -> Out { n = %s }
                """.formatted(DECLS, type, constructsIn(type), probeFor(type), fixture, expected));
        return true;
    }

    /** The same type as a behavior input, read and applied through {@link JsonBoundary} — what
     *  {@code souther run} drives, without the command line around it. */
    private String runReads(String type, String json) throws Exception {
        return Crossing.of(sourceTaking(type), "demo", "take", json);
    }

    private static String sourceTaking(String type) {
        return """
                module demo
                %s
                behavior take : (v: %s) -> Int%s
                let take (v) = %s
                """.formatted(DECLS, type, constructsIn(type).replace(", ", " constructs "),
                        probeFor(type));
    }

    /**
     * An expression reducing a value of that type to the Int the three paths compare.
     *
     * <p>A map is read by looking its key up, written as the key type — never by counting its
     * entries. Erasure is what makes the difference: a reader that hands the behavior the strings
     * the object carried, having never turned them into keys, still answers a count, and only a
     * lookup written in the key type misses.
     */
    private static String probeFor(String type) {
        if (type.equals("Map<Outcome, Int>")) {
            // a case value written in an argument position types as the case, not as the sum, so
            // this row reads the keys it was given rather than looking one up
            return "List.length(List.filter((k) -> k == Won, Map.keys(v)))";
        }
        if (type.startsWith("Map<")) {
            return "Option.withDefault(0, Map.get(" + keyIn(type) + ", v))";
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

    /** The key the row's map holds, written as a value of the key type. */
    private static String keyIn(String mapType) {
        return switch (mapType) {
            case "Map<String, Int>" -> "\"a\"";
            case "Map<Key, Int>" -> "Key(\"a\")";
            case "Map<Date, Int>" -> "Date(\"2026-01-01\")";
            case "Map<Time, Int>" -> "Time(\"09:30:00\")";
            case "Map<Instant, Int>" -> "Instant(\"2026-01-01T09:00:00Z\")";
            case "Map<DateTime, Int>" -> "DateTime(\"2026-01-01T09:00\")";
            case "Map<Bounded, Int>" -> "Bounded(\"abc\")";
            case "Map<Day, Int>" -> "Day(Date(\"2026-01-01\"))";
            default -> throw new IllegalArgumentException(mapType);
        };
    }

    /** What the probe builds, for the `constructs` the behavior running it needs. A temporal is
     *  written with a primitive's constructor, which is nobody's to declare. */
    private static String constructsIn(String type) {
        if (type.contains("Key")) {
            return ", Key";
        }
        if (type.contains("Bounded")) {
            return ", Bounded";
        }
        if (type.contains("Day")) {
            return ", Day";
        }
        return type.contains("Outcome") ? ", Won" : "";
    }
}
