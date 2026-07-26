package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;
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
 * without the others fails here rather than in whatever example happens to use it. Where they do not
 * agree today the divergence is stated, not smoothed over: a test that hides a gap is worse than the
 * gap.
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

    // === where they part ===

    /**
     * A newtype-keyed map crosses the boundary and is written in a fixture, and {@code run} declines
     * it. {@code Runner.decoderFor} handles only a {@code String} key; its javadoc says so, so this
     * is a stated limit rather than a surprise — stated here too, so closing it in one place without
     * the others is caught.
     */
    @Test
    void aNewtypeKeyedMapIsReadByTheBoundaryAndTheFixtureButNotByRun() throws Exception {
        assertTrue(boundaryReads("Map<Key, Int>", Map.of("a", 1L)), "the derived codec reads it");
        assertTrue(fixtureReads("Map<Key, Int>", "[ (Key(\"a\"), 1) ]", 1L), "a fixture writes it");

        RuntimeException e = assertThrows(Runner.RunException.class,
                () -> runReads("Map<Key, Int>", "{\"a\": 1}"));
        assertTrue(e.getMessage().contains("Map"), e.getMessage());
    }

    /** A temporal-keyed map, added at the boundary by issue #100, is the same story one step later. */
    @Test
    void aDateKeyedMapIsReadByTheBoundaryAndTheFixtureButNotByRun() throws Exception {
        assertTrue(boundaryReads("Map<Date, Int>", Map.of("2026-01-01", 1L)),
                "the derived codec reads it");
        assertTrue(fixtureReads("Map<Date, Int>", "[ (Date(\"2026-01-01\"), 1) ]", 1L),
                "a fixture writes it");

        assertThrows(Runner.RunException.class, () -> runReads("Map<Date, Int>", "{\"2026-01-01\": 1}"));
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
            default -> throw new IllegalArgumentException(type);
        };
    }

    /** A data with a field of that type, decoded through its generated codec. */
    private boolean boundaryReads(String type, Object neutral) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo
                data Key = String
                data Wrapped = Int
                data Holder = { v: %s }
                """.formatted(type)), getClass().getClassLoader());
        Object decoded = Codecs.decode(loader, "demo.Holder", Map.of("v", neutral));
        return "Ok".equals(decoded.getClass().getSimpleName());
    }

    /** A behavior taking that type, with an `example` whose fixture writes it. The compile evaluates
     *  the example, so a fixture the builder cannot construct fails the compile. */
    private boolean fixtureReads(String type, String fixture, Object expected) {
        Compiler.compile("""
                module demo
                data Key = String
                data Wrapped = Int
                data Out = { n: Int }
                behavior take : (v: %s) -> Out constructs Out
                let take (v) = Out { n = %s }
                example take
                  | "reads it" : (%s) -> Out { n = %s }
                """.formatted(type, sizeExprFor(type), fixture, expected));
        return true;
    }

    /** The same type as a behavior input, driven through {@code souther run}. */
    private String runReads(String type, String json) throws Exception {
        Path file = dir.resolve("run" + Math.abs(type.hashCode()) + ".sou");
        Files.writeString(file, """
                module demo
                data Key = String
                data Wrapped = Int
                behavior take : (v: %s) -> Int
                let take (v) = %s
                """.formatted(type, sizeExprFor(type)));
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
        return type.equals("Wrapped") ? "v.value" : "v";
    }
}
