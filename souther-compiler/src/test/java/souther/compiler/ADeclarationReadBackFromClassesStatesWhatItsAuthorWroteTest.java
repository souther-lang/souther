package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A declaration reached through a dependency's published classes says what its author wrote, down
 * to the definitions the author never exposed.
 *
 * <p>The third of the three the spec puts on one footing: a type declared in this module, one
 * imported from a module compiled in the same run, and one imported from a module compiled
 * separately and reached through its classes all state the same invariant
 * (spec §invariant-discharge-representation). The first two are held next door; this is the one
 * where nothing of the library is in the room but its artifact.
 *
 * <p><b>The {@code let} is deliberately not exposed.</b> It is what the clause is composed out of,
 * and an importer has no name for it — so a reading that tried to work the clause out here could
 * not, however it went about it. What makes this work is not that the definition is importable but
 * that the artifact carries what the declaration cannot be read without, and the clause is expanded
 * where it was written. Exposed, the test would pass for a reason that says nothing: the consumer
 * would have a name for the value and a reading built the wrong way round would still reach it.
 *
 * <p>Held against the literal clause beside it rather than against a form of words. Both are read
 * to the end, so both come to the same measure; if the composed one is not read, its measure moves
 * and the literal one does not.
 */
class ADeclarationReadBackFromClassesStatesWhatItsAuthorWroteTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** The dependency, whose {@code exposing} does not name the value the clause is composed from. */
    private static final String LIBRARY = """
            module shared.codes exposing ( Composed, Written )

            let tail = "[0-9]{3}"

            data Composed = String
                invariant String.matches("00" ++ tail, value)

            data Written = String
                invariant String.matches("00[0-9]{3}", value)
            """;

    /** The consumer, which has the dependency's classes and none of its source. */
    private static final String CONSUMER = """
            module app.intake exposing ( onComposed, onWritten )

            import shared.codes ( Composed, Written )

            data Yes
            data No

            behavior onComposed : (i: Composed) -> Yes | No
            let onComposed (i) = Yes

            example onComposed
                | "one" : (Composed("00123")) -> Yes

            behavior onWritten : (i: Written) -> Yes | No
            let onWritten (i) = Yes

            example onWritten
                | "one" : (Written("00123")) -> Yes
            """;

    /** How far the rules about each behavior's position were read, in the consumer's own report. */
    private static Map<String, JsonNode> readInTheConsumer() {
        Map<String, ClassFileImage> published = Compiler.compile(LIBRARY);
        Compilation compilation =
                Compilation.ofSource(CONSUMER, "Main", ModulePath.of(published));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        JsonNode document = JSON.readTree(
                AdequacyReport.of(compilation).json(SourceNameResolver.identity()));
        Map<String, JsonNode> out = new LinkedHashMap<>();
        for (JsonNode module : document.get("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                out.put(behavior.path("name").asString(),
                        behavior.path("partition").path("axesMeasure"));
            }
        }
        return out;
    }

    @Test
    void aClauseComposedFromAnUnexposedValueIsReadAsFarAsOneWrittenOut() {
        Map<String, JsonNode> read = readInTheConsumer();
        assertNotNull(read.get("onComposed"), "the consumer measures the composed clause");
        assertNotNull(read.get("onWritten"), "and the written one beside it");

        assertEquals(read.get("onWritten"), read.get("onComposed"),
                "a clause composed from a value the dependency never exposed is read here as far"
                        + " as one written out, because the artifact carries what the declaration"
                        + " cannot be read without and the clause is expanded where it was written");
    }

    /** And nothing of the dependency was rebuilt here to make that true. */
    @Test
    void theConsumerEmitsNothingOfTheDependency() {
        Map<String, ClassFileImage> app = Compiler.compileModules(
                java.util.List.of(CONSUMER), ModulePath.of(Compiler.compile(LIBRARY)));

        assertEquals(java.util.List.of(),
                app.keySet().stream().filter(each -> each.startsWith("shared.codes")).toList(),
                "the dependency's classes are its own build's");
    }
}
