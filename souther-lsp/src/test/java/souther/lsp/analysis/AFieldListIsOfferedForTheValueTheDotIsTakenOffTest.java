package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.CompletionItem;
import souther.lsp.protocol.Position;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What may be written after a {@code .} is a field of the value it is taken off, and nothing else in
 * scope. Asked at the editor's own surface, on a buffer that does not parse — which is every buffer
 * a field list is wanted on.
 */
class AFieldListIsOfferedForTheValueTheDotIsTakenOffTest {

    private static final String LIB_URI = "file:///lib.sou";
    private static final String MODEL_URI = "file:///m.sou";

    private static final String LIB = """
            module lib exposing ( Cost )

            data Cost = { amount: Int, currency: Text }
            """;

    private static String model(String body) {
        return """
                module m

                import lib ( Cost )

                data Draft = { plannedCost: Cost, note: Text }

                behavior submit : (request: Draft) -> Int
                let submit (request) = \
                """ + body;
    }

    @Test
    void theFieldsOfTheTypeTheSignatureSaysArrive() {
        assertEquals(List.of("plannedCost", "note"), labelsAfterTheDot(model("request.\n")),
                "`request` arrives as a `Draft`, which the behavior line says");
    }

    @Test
    void andTheFieldsOfWhatAFieldIsDeclaredToBe() {
        assertEquals(List.of("amount", "currency"),
                labelsAfterTheDot(model("request.plannedCost.\n")),
                "`plannedCost` is a `Cost`, which another module's data declaration says");
    }

    @Test
    void andNothingElseThatIsInScope() {
        List<String> offered = labelsAfterTheDot(model("request.\n"));

        assertFalse(offered.contains("submit"), "a behavior is not a field of a `Draft`");
        assertFalse(offered.contains("let"), "and neither is a keyword");
    }

    @Test
    void aValueNoDeclarationSpeaksForIsOfferedNothingRatherThanEverything() {
        List<CompletionItem> offered = completions("""
                module m

                data Draft = { plannedCost: Int }

                behavior make : () -> Draft
                behavior submit : (request: Draft) -> Int
                let submit (request) = make().
                """);

        assertTrue(offered.isEmpty(),
                "a call's answer is a value this reading cannot type, and what may be written after"
                        + " the dot is not every name in scope");
    }

    @Test
    void whereThereIsNoDotTheNameListIsWhatIsOffered() {
        // The same document, finished. Nothing here is a field read, so what may be written is
        // whatever is in scope — which is the list this server already offered.
        List<String> offered = labelsOf(completions(model("request.note\n")));

        assertTrue(offered.contains("submit"), "the behaviors of the module are still offered");
        assertTrue(offered.contains("let"), "and so are the keywords");
    }

    private static List<String> labelsAfterTheDot(String text) {
        return labelsOf(completions(text));
    }

    private static List<String> labelsOf(List<CompletionItem> items) {
        List<String> labels = new ArrayList<>();
        for (CompletionItem item : items) {
            labels.add(item.label());
        }
        return labels;
    }

    /** What the editor is offered with the cursor at the end of the last written line. */
    private static List<CompletionItem> completions(String text) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(LIB_URI, LIB);
        sources.put(MODEL_URI, text);
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);

        List<String> lines = text.lines().toList();
        int last = lines.size() - 1;
        return analyzer.completions(MODEL_URI, new Position(last, lines.get(last).length()), graph);
    }
}
