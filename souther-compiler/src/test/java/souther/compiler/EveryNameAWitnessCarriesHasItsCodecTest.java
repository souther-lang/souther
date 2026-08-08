package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A boundary witness carries a name a model declared, and every such name has the codec the runner
 * reaches for. So the runner asking for one is not a question that can be answered no: it is reading
 * what the signature already admitted.
 *
 * <p>Held over every shape the witness has a name in — a record, a newtype, a unit, an enumeration,
 * a sum, a union a behavior answers with, and both kinds of named map key — in both directions,
 * which is every place the runner turns a name into a factory.
 */
class EveryNameAWitnessCarriesHasItsCodecTest {

    @TempDir
    Path dir;

    private static final String MODEL = """
            module demo exposing ( Sku, Empty, Stage, Note, Keyed, nominal, newtype, unit, sum, keys, answer )

            data Sku = String
            data Empty
            data Won
            data Lost
            data Stage = Won | Lost
            data Note = { at: DateTime, sku: Sku }
            data Keyed = { by: Map<Sku, Int>, at: Map<Stage, Int> }

            behavior nominal : (n: Note) -> Note
            let nominal (n) = n

            behavior newtype : (s: Sku) -> Sku
            let newtype (s) = s

            behavior unit : (e: Empty) -> Empty
            let unit (e) = e

            behavior sum : (s: Stage) -> Stage
            let sum (s) = s

            behavior keys : (k: Keyed) -> Keyed
            let keys (k) = k

            behavior answer : (n: Int) -> Note | Empty
                constructs Note, Empty, Sku
            let answer (n) =
                if n > 0 then Note { at = DateTime("2026-01-01T00:00:00"), sku = Sku("s") } else Empty
            """;

    private Path model() throws Exception {
        Path file = dir.resolve("demo.sou");
        Files.writeString(file, MODEL);
        return file;
    }

    private String run(String behavior, String input) throws Exception {
        return Runner.run(model(), behavior, input);
    }

    @Test
    void aRecordCarriesItsNameInBothDirections() throws Exception {
        String note = "{\"at\":\"2026-01-01T00:00\",\"sku\":\"s\"}";
        assertEquals(note, run("nominal", note));
    }

    @Test
    void aNewtypeCarriesItsNameInBothDirections() throws Exception {
        assertEquals("\"s\"", run("newtype", "\"s\""));
    }

    @Test
    void aUnitCarriesItsNameInBothDirections() throws Exception {
        assertEquals("{}", run("unit", "{}"));
    }

    @Test
    void anEnumerationCarriesItsNameInBothDirections() throws Exception {
        assertEquals("\"Won\"", run("sum", "\"Won\""));
    }

    @Test
    void bothKindsOfNamedMapKeyCarryTheirNameInBothDirections() throws Exception {
        String keyed = "{\"by\":{\"s\":1},\"at\":{\"Won\":2}}";
        assertEquals(keyed, run("keys", keyed));
    }

    @Test
    void aUnionABehaviorAnswersWithCarriesTheNamesOfItsMembers() throws Exception {
        assertEquals("{\"at\":\"2026-01-01T00:00\",\"sku\":\"s\",\"type\":\"Note\"}",
                run("answer", "1"));
        assertEquals("{\"type\":\"Empty\"}", run("answer", "0"));
    }
}
