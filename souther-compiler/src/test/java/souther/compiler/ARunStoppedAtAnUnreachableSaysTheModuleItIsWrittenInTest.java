package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a run stops at an {@code unreachable}, what reads the run is told the module whose text the
 * {@code unreachable} is written in and the line and column it is at there.
 *
 * <p>An {@code unreachable} of another module's helper is inlined into the class of the behavior
 * calling it, and the class's line table names only its own text, so the message the abort prints
 * says the reason and no numbers. The place travels beside the message, as a refused construction's
 * does, and names the helper's module and its line there.
 */
class ARunStoppedAtAnUnreachableSaysTheModuleItIsWrittenInTest {

    private static final String LIB = """
            module lib

            let pick (n: Int): Int = if n * n - 1 >= 1 then n else unreachable "never this small"
            """;

    private static final String APP = """
            module app

            import lib (pick)

            behavior go : (n: Int) -> Int
            let go (n) = pick(n)
            """;

    private static final String UNREACHABLE = "unreachable \"never this small\"";

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void anUnreachableOfAnInlinedHelperIsPlacedInTheHelpersModule() {
        Compilation compilation = Compilation.ofSources(List.of(LIB, APP), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");
        int at = LIB.indexOf(UNREACHABLE);
        String before = LIB.substring(0, at);
        int line = (int) before.chars().filter(c -> c == '\n').count() + 1;
        int column = at - before.lastIndexOf('\n');

        assertEquals(List.of(JSON.readTree("""
                        [{"at": "an_unreachable", "said": "never this small", "module": "lib",
                          "sourceId": "%s", "line": %d, "column": %d}]"""
                        .formatted(compilation.sourceIdOf("lib").value(), line, column))),
                stopsOf(compilation, "go"));

        String human = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
        String lib = SourceRendering.namedByIdentity(compilation.texts()).names()
                .nameOf(compilation.sourceIdOf("lib"));
        assertTrue(human.contains("an `unreachable` at " + lib + ":" + line + ":" + column
                        + " (never this small)"),
                () -> "the report names the helper's line: " + human);
    }

    /** Every `runsStopped` the document writes under app's {@code behavior}, after holding the
     *  document to its schema. */
    private static List<JsonNode> stopsOf(Compilation compilation, String behavior) {
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        for (JsonNode module : document.path("modules")) {
            if (!module.path("module").asString().equals("app")) {
                continue;
            }
            for (JsonNode each : module.path("behaviors")) {
                if (each.path("name").asString().equals(behavior)) {
                    List<JsonNode> out = new ArrayList<>();
                    for (JsonNode obligation : each.path("decision").path("obligations")) {
                        for (JsonNode shortfall : obligation.path("synthesisShortfalls")) {
                            if (shortfall.has("runsStopped")) {
                                out.add(shortfall.path("runsStopped"));
                            }
                        }
                    }
                    return out;
                }
            }
        }
        throw new AssertionError("the document says nothing of " + behavior + ": " + document);
    }
}
