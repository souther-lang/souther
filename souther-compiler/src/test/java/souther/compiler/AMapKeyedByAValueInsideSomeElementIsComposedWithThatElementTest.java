package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row where some element of a list is filed in a map is composed with that element, and the map
 * is keyed by what stands inside it.
 *
 * <p>Said as the statement it is: some element of {@code items}, and some entry of {@code shelf}
 * whose key is the element's {@code sku}. The value handed to the map is read off the list once it
 * is built, so the list has to be built with an element to read it off — and has to hold one,
 * since a row meeting the statement does. A list chosen whole has no element the row could name,
 * and the map would be asked for a key nothing wrote.
 *
 * <p>Asked of the forms the value takes inside the element — the element itself, a field of it, a
 * field of a field, and a field read beside another the statement also asks of — because each is a
 * position under the element and none of them is what the list is built around.
 */
class AMapKeyedByAValueInsideSomeElementIsComposedWithThatElementTest {

    private static final String FIELD = """
            module p
            import List ( filterMap, length )
            data Item = { sku: String, q: Int }
            behavior pick : (items: List<Item>, shelf: Map<String, String>) -> Int
            let pick (items, shelf) = {
                let pickable = filterMap(i -> Map.get(i.sku, shelf), items)
                if length(pickable) >= 1 then 1 else 0
            }
            example pick
                | "nothing filed" : ([], []) -> 0
            """;

    private static final String NESTED = """
            module p
            import List ( filterMap, length )
            data Meta = { sku: String }
            data Item = { meta: Meta, q: Int }
            behavior pick : (items: List<Item>, shelf: Map<String, String>) -> Int
            let pick (items, shelf) = {
                let pickable = filterMap(i -> Map.get(i.meta.sku, shelf), items)
                if length(pickable) >= 1 then 1 else 0
            }
            example pick
                | "nothing filed" : ([], []) -> 0
            """;

    private static final String ITSELF = """
            module p
            import List ( filterMap, length )
            behavior pick : (items: List<String>, shelf: Map<String, String>) -> Int
            let pick (items, shelf) = {
                let pickable = filterMap(k -> Map.get(k, shelf), items)
                if length(pickable) >= 1 then 1 else 0
            }
            example pick
                | "nothing filed" : ([], []) -> 0
            """;

    private static final String BESIDE_ANOTHER_FIELD = """
            module p
            import List ( filterMap, length )
            data Item = { sku: String, q: Int }
            behavior pick : (items: List<Item>, shelf: Map<String, String>) -> Int
            let pick (items, shelf) = {
                let pickable = filterMap(i -> Map.get(i.sku, shelf),
                    List.filter(i -> i.q > 0, items))
                if length(pickable) >= 1 then 1 else 0
            }
            example pick
                | "nothing filed" : ([], []) -> 0
            """;

    /**
     * A list the rules keep empty, asked for the statement that some element of it is filed.
     *
     * <p>The model's answer, and no figure of this compiler's: the statement needs an element and
     * the rules leave no room for one, so no row meets it however far a search went.
     */
    private static final String KEPT_EMPTY = """
            module p
            import List ( filterMap, length )
            data Keys = List<String>
                invariant none = List.length(value) <= 0
            behavior pick : (ks: Keys, shelf: Map<String, String>) -> Int
            let pick (ks, shelf) = {
                let pickable = filterMap(k -> Map.get(k, shelf), ks.value)
                if length(pickable) >= 1 then 1 else 0
            }
            example pick
                | "nothing filed" : (Keys([]), []) -> 0
            """;

    /** Each form, with the row composed for the rule where some element is filed. */
    private static final Map<String, List<String>> COMPOSED = Map.of(
            FIELD, List.of("[Item { sku = \"x\", q = 0 }]", "[(\"x\", \"x\")]"),
            NESTED, List.of("[Item { meta = Meta { sku = \"x\" }, q = 0 }]",
                    "[(\"x\", \"x\")]"),
            ITSELF, List.of("[\"x\"]", "[(\"x\", \"x\")]"),
            BESIDE_ANOTHER_FIELD, List.of("[Item { sku = \"x\", q = 1 }]", "[(\"x\", \"x\")]"));

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> errors(Compilation compilation) {
        return compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                .toList();
    }

    /** The rows composed for the rules no row takes, each as the texts of its inputs. */
    private static List<List<String>> composedForTheRules(Compilation compilation) {
        Adequacy.Filling filling = Adequacy.generatedOf(compilation.db(),
                compilation.modules().get(0)).get("pick");
        List<List<String>> out = new ArrayList<>();
        filling.generation().stream()
                .filter(each -> each.finding().about() instanceof About.ARuleNoRowTakes)
                .forEach(each -> {
                    GenerationOutcome.Generated made = assertInstanceOf(
                            GenerationOutcome.Generated.class, each.outcome(),
                            () -> "a row is composed for the rule: " + each.outcome());
                    made.candidates().forEach(row -> out.add(
                            row.inputs().stream().map(FixtureTemplate::text).toList()));
                });
        return out;
    }

    /** The list is built holding the element, and the map is keyed by what stands inside it. */
    @Test
    void eachFormIsComposedWithTheElementTheMapIsKeyedBy() {
        COMPOSED.forEach((model, expected) -> assertEquals(List.of(expected),
                composedForTheRules(measured(model)), model));
    }

    /**
     * The rows composed, put back as examples, take the rule they were composed for: the model
     * answers each as filed, and no rule is left that no row takes.
     */
    @Test
    void theRowsComposedTakeTheRuleTheyWereComposedFor() {
        COMPOSED.forEach((model, expected) -> {
            Compilation answered = measured(model + "    | \"filed\" : ("
                    + String.join(", ", expected) + ") -> 1\n");

            assertEquals(List.of(), errors(answered), model);
            assertFalse(report(answered).contains("no row takes a decision rule"),
                    () -> report(answered));
        });
    }

    /** The control: the same rows answered as nothing filed are refused. */
    @Test
    void theSameRowsAnsweredAsNothingFiledAreRefused() {
        COMPOSED.forEach((model, expected) -> assertFalse(errors(measured(model
                + "    | \"filed\" : (" + String.join(", ", expected) + ") -> 0\n")).isEmpty(),
                model));
    }

    /**
     * A list the rules keep empty is answered as the model's: nothing filtered out of it holds one,
     * so the comparison never comes out true on any way there, and the rule needing it to is out
     * before anything is composed.
     */
    @Test
    void aListTheRulesKeepEmptyIsTheModelsAnswer() {
        String report = report(measured(KEPT_EMPTY));

        assertTrue(report.contains("no row is owed at 1 decision rule — its way needs a comparison"
                + " to come out one way, but no value can reach it coming out so"), report);
    }
}
