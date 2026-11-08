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

/**
 * Where a run stops at a construction, what reads the run is told the module whose text the
 * construction is written in and the line and column it is at there, and the module the invariant
 * that refused it is declared in.
 *
 * <p>Three ways a construction can be in another module than the behavior that ran. A helper of
 * another module is inlined into the class of the behavior calling it, and the class's line table
 * names only its own text; the construction is still written in the helper's module, at the line
 * of that module's text. A behavior of another module is run as itself. And where two modules each
 * declare a type of one name with an invariant, the rule that refused the run is the one declared
 * where the type built is, which a handle naming the type alone does not say.
 */
class ARunStoppedAtAConstructionSaysTheModuleItIsWrittenInTest {

    private static final String LIB_HELPER = """
            module lib

            data Positive = { n: Int }
                invariant n >= 1

            let make (n: Int): Positive = Positive { n = n * n - 1 }
            """;

    private static final String APP = """
            module app

            import lib (Positive, make)

            behavior go : (n: Int) -> Positive
            let go (n) = make(n)
            """;

    private static final String LIB_BEHAVIOR = """
            module lib

            data Positive = { n: Int }
                invariant n >= 1

            behavior make : (n: Int) -> Positive
                constructs Positive
            let make (n) = Positive { n = n * n - 1 }
            """;

    private static final String LIB_COUNT = """
            module lib

            data Positive = { n: Int }
                invariant n >= 1

            let make (n: Int): Int = {
                let p = Positive { n = n * n - 1 }
                p.n
            }
            """;

    private static final String APP_OWN = """
            module app

            import lib (make)

            data Positive = { n: Int }
                invariant n >= 1

            behavior go : (n: Int) -> Positive
                constructs Positive
            let go (n) = Positive { n = make(n) + 1 }
            """;

    private static final String CONSTRUCTION = "Positive { n = n * n - 1 }";

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** The helper's body runs in app's class, and its construction is written in lib. */
    @Test
    void aConstructionOfAnInlinedHelperIsPlacedInTheHelpersModule() {
        Compilation compilation = compiled(LIB_HELPER, APP);

        assertEquals(List.of(stoppedAt(compilation, LIB_HELPER)), stopsOf(compilation, "go"));
    }

    @Test
    void aConstructionOfADependencyBehaviorIsPlacedInItsModule() {
        Compilation compilation = compiled(LIB_BEHAVIOR, APP);

        assertEquals(List.of(stoppedAt(compilation, LIB_BEHAVIOR)), stopsOf(compilation, "go"));
    }

    /** Both modules declare `Positive`; the run stops at lib's, and app's never refuses it. */
    @Test
    void ofTwoTypesOfOneNameTheRuleIsTheOneTheBuiltTypesModuleDeclares() {
        Compilation compilation = compiled(LIB_COUNT, APP_OWN);

        assertEquals(List.of(stoppedAt(compilation, LIB_COUNT)), stopsOf(compilation, "go"));
    }

    private static Compilation compiled(String... sources) {
        Compilation compilation = Compilation.ofSources(List.of(sources), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");
        return compilation;
    }

    /** What the document says of a run stopped at lib's construction written in {@code lib}. */
    private static JsonNode stoppedAt(Compilation compilation, String lib) {
        int at = lib.indexOf(CONSTRUCTION);
        String before = lib.substring(0, at);
        return JSON.readTree("""
                [{"at": "a_construction", "rule": "invariant Positive #1", "module": "lib",
                  "declaredIn": "lib", "sourceId": "%s", "line": %d, "column": %d}]"""
                .formatted(compilation.sourceIdOf("lib").value(),
                        (int) before.chars().filter(c -> c == '\n').count() + 1,
                        at - before.lastIndexOf('\n')));
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
