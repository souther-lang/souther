package souther.cli;

import org.junit.jupiter.api.io.TempDir;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.stream.Stream;

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

    static Stream<Arguments> everyTypeAndAValueOfIt() {
        return Stream.of(
                // the primitives and the named types
                Arguments.of("Int", "7"),
                Arguments.of("String", "\"k\""),
                Arguments.of("Date", "Date(\"2026-01-01\")"),
                Arguments.of("Code", "Code(\"c\")"),
                Arguments.of("Outcome", "Won"),
                Arguments.of("Closed", "Closed"),
                // the collections
                Arguments.of("List<Int>", "[ 1, 2 ]"),
                Arguments.of("Set<String>", "Set.fromList([ \"b\", \"a\" ])"),
                Arguments.of("Map<String, Code>", "Map.fromList([ (\"k\", Code(\"v\")) ])"),
                // the kinds a boundary map may be keyed by
                Arguments.of("Map<String, Int>", "Map.fromList([ (\"k\", 7) ])"),
                Arguments.of("Map<Code, Int>", "Map.fromList([ (Code(\"k\"), 7) ])"),
                Arguments.of("Map<Date, Int>", "Map.fromList([ (Date(\"2026-01-01\"), 7) ])"),
                Arguments.of("Map<Time, Int>", "Map.fromList([ (Time(\"09:30:00\"), 7) ])"),
                Arguments.of("Map<Instant, Int>",
                        "Map.fromList([ (Instant(\"2026-01-01T09:00:00Z\"), 7) ])"),
                Arguments.of("Map<DateTime, Int>",
                        "Map.fromList([ (DateTime(\"2026-01-01T09:00\"), 7) ])"),
                Arguments.of("Map<Outcome, Int>", "Map.fromList([ (Won, 7) ])"),
                // A newtype over a temporal, which holds the two paths to one key rendering: each
                // renders a named key through that type's own encoder, so neither can learn a base
                // the other does not have.
                Arguments.of("Map<Day, Int>", "Map.fromList([ (Day(Date(\"2026-01-01\")), 7) ])"),
                // and at depth, where the key is not the type the behavior declared
                Arguments.of("List<Map<Code, Int>>", "[ Map.fromList([ (Code(\"k\"), 7) ]) ]"),
                Arguments.of("Map<String, Map<Code, Int>>",
                        "Map.fromList([ (\"a\", Map.fromList([ (Code(\"k\"), 7) ])) ])"),
                Arguments.of("List<Map<Day, Int>>",
                        "[ Map.fromList([ (Day(Date(\"2026-01-01\")), 7) ]) ]"));
    }

    /** The value written bare, and written as the sole field of a data — the second being the first
     *  inside an object, since the field's own codec is what a data's encoder calls. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("everyTypeAndAValueOfIt")
    void aValueIsWrittenTheSameBothWays(String type, String value) throws Exception {
        String bare = written(type, value, "bare");
        String wrapped = written(type, value, "wrapped");
        assertEquals("{\"v\":" + bare + "}", wrapped,
                "a " + type + " writes the same whether `run` composes it or the derived codec does");
    }

    /** Runs one of the two behaviors and returns the JSON it wrote. */
    private String written(String type, String value, String behavior) throws Exception {
        Path file = dir.resolve(
                "w" + Integer.toUnsignedString((type + value).hashCode()) + ".sou");
        String built = builtBy(value);
        Files.writeString(file, """
                module demo
                data Code = String
                data Day = Date
                data Outcome = Won | Lost
                data Closed
                data Holder = { v: %s }
                behavior bare : (n: Int) -> %s%s
                let bare (n) = %s
                behavior wrapped : (n: Int) -> Holder constructs Holder%s
                let wrapped (n) = Holder { v = %s }
                """.formatted(type, type, built.isEmpty() ? "" : " constructs " + built,
                        value, built.isEmpty() ? "" : ", " + built, value));
        return Runner.run(file, behavior, "1").trim();
    }

    /** What the value expression builds that belongs in `constructs`, for the clause both behaviors
     *  need. A row builds at most one of the module's data types, which is what keeps this a lookup
     *  rather than a parse. A row writing `Won` or `Closed` builds a unit, which is in no construction set
     *  (spec §constructs-excludes-unit-data), so it leaves the clause empty. */
    private static String builtBy(String value) {
        if (value.contains("Code(")) {
            return "Code";
        }
        return value.contains("Day(") ? "Day" : "";
    }
}
