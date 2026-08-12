package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two implementations answer "write a value of type T to the outside": the codec derived for a data,
 * and {@code Runner.encode} behind {@code souther run}. A data's field reaches the first, and a
 * behavior's own output type reaches the second — so the same value written the two ways has to come
 * out the same, and where it does not, {@code run} is a boundary of its own with its own rules.
 *
 * <p>The comparison is that identity. For each type in the table one behavior answers with the bare
 * value and another answers with a data holding it, and the second must be the first inside
 * {@code {"v": …}} — byte for byte, since what a boundary writes is fixed rather than merely
 * equivalent. Wrapping is what routes the value through the derived codec, so the two paths meet on
 * one value and disagree only where they were written to disagree.
 *
 * <p>The fixture builder an {@code example} uses is not a third path here, as it is on the reading
 * side ({@link DecoderPathAgreementTest}): an example builds its expected value and compares domain
 * values, so it reads a written form in and never writes one out.
 */
class EncoderPathAgreementTest {

    @TempDir
    Path dir;

    // === the primitives and the named types ===

    @Test
    void anIntIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Int", "7");
    }

    @Test
    void aStringIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("String", "\"k\"");
    }

    @Test
    void aDateIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Date", "Date(\"2026-01-01\")");
    }

    @Test
    void aNewtypeIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Code", "Code(\"c\")");
    }

    @Test
    void anEnumerationIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Outcome", "Won");
    }

    // === the collections ===

    @Test
    void aListIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("List<Int>", "[ 1, 2 ]");
    }

    @Test
    void aSetIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Set<String>", "Set.fromList([ \"b\", \"a\" ])");
    }

    @Test
    void aMapValueOfANamedTypeIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Map<String, Code>", "Map.fromList([ (\"k\", Code(\"v\")) ])");
    }

    // === the kinds a boundary map may be keyed by ===

    @Test
    void aStringKeyedMapIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Map<String, Int>", "Map.fromList([ (\"k\", 7) ])");
    }

    @Test
    void aNewtypeKeyedMapIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Map<Code, Int>", "Map.fromList([ (Code(\"k\"), 7) ])");
    }

    @Test
    void aDateKeyedMapIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Map<Date, Int>", "Map.fromList([ (Date(\"2026-01-01\"), 7) ])");
    }

    @Test
    void aTimeKeyedMapIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Map<Time, Int>", "Map.fromList([ (Time(\"09:30:00\"), 7) ])");
    }

    @Test
    void anInstantKeyedMapIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Map<Instant, Int>",
                "Map.fromList([ (Instant(\"2026-01-01T09:00:00Z\"), 7) ])");
    }

    @Test
    void aDateTimeKeyedMapIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Map<DateTime, Int>", "Map.fromList([ (DateTime(\"2026-01-01T09:00\"), 7) ])");
    }

    @Test
    void anEnumerationKeyedMapIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Map<Outcome, Int>", "Map.fromList([ (Won, 7) ])");
    }

    /** A newtype over a temporal. This is the row that holds the two paths to one key rendering:
     *  each renders a named key through that type's own encoder, so neither can learn a base the
     *  other does not have (issue #636). */
    @Test
    void aWrappedTemporalKeyedMapIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Map<Day, Int>", "Map.fromList([ (Day(Date(\"2026-01-01\")), 7) ])");
    }

    // === and at depth, where the key is not the type the behavior declared ===

    @Test
    void aListOfNewtypeKeyedMapsIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("List<Map<Code, Int>>", "[ Map.fromList([ (Code(\"k\"), 7) ]) ]");
    }

    @Test
    void aMapOfNewtypeKeyedMapsIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("Map<String, Map<Code, Int>>",
                "Map.fromList([ (\"a\", Map.fromList([ (Code(\"k\"), 7) ])) ])");
    }

    @Test
    void aListOfWrappedTemporalKeyedMapsIsWrittenTheSameBothWays() throws Exception {
        writtenAlike("List<Map<Day, Int>>", "[ Map.fromList([ (Day(Date(\"2026-01-01\")), 7) ]) ]");
    }

    // === the two paths ===

    /** The value written bare, and written as the sole field of a data — the second being the first
     *  inside an object, since the field's own codec is what a data's encoder calls. */
    private void writtenAlike(String type, String value) throws Exception {
        String bare = written(type, value, "bare");
        String wrapped = written(type, value, "wrapped");
        assertEquals("{\"v\":" + bare + "}", wrapped,
                "a " + type + " writes the same whether `run` composes it or the derived codec does");
    }

    /** Runs one of the two behaviors and returns the JSON it wrote. */
    private String written(String type, String value, String behavior) throws Exception {
        Path file = dir.resolve("w" + Math.abs((type + value).hashCode()) + ".sou");
        String built = builtBy(value);
        Files.writeString(file, """
                module demo
                data Code = String
                data Day = Date
                data Outcome = Won | Lost
                data Holder = { v: %s }
                behavior bare : (n: Int) -> %s%s
                let bare (n) = %s
                behavior wrapped : (n: Int) -> Holder constructs Holder%s
                let wrapped (n) = Holder { v = %s }
                """.formatted(type, type, built.isEmpty() ? "" : " constructs " + built,
                        value, built.isEmpty() ? "" : ", " + built, value));
        return Runner.run(file, behavior, "1").trim();
    }

    /** What the value expression builds, for the `constructs` both behaviors need. A row builds at
     *  most one of the module's data types, which is what keeps this a lookup rather than a parse. */
    private static String builtBy(String value) {
        if (value.contains("Code(")) {
            return "Code";
        }
        if (value.contains("Day(")) {
            return "Day";
        }
        return value.contains("Won") ? "Won" : "";
    }
}
