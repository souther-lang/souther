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

/**
 * A row where so many elements of a list are filed in a map is composed, and the map is made to
 * hold a key for each element counted.
 *
 * <p>Said as the count it is: how many elements of {@code items} some entry of {@code shelf} is
 * keyed by. Whether an element is counted is what the map holds, so the list is composed at a size
 * the count asks with every element counted, and the map is handed a key for each — and at a count
 * of none, none of them is a key of it.
 */
class SoManyElementsOfAListFiledInAMapAreComposedTest {

    private static final String ITSELF = """
            module p
            import List ( filterMap, length )
            behavior pick : (items: List<String>, shelf: Map<String, String>) -> Int
            let pick (items, shelf) = {
                let pickable = filterMap(k -> Map.get(k, shelf), items)
                if length(pickable) >= 2 then 1 else 0
            }
            example pick
                | "nothing filed" : ([], []) -> 0
            """;

    private static final String FIELD = """
            module p
            import List ( filterMap, length )
            data Item = { sku: String, q: Int }
            behavior pick : (items: List<Item>, shelf: Map<String, String>) -> Int
            let pick (items, shelf) = {
                let pickable = filterMap(i -> Map.get(i.sku, shelf), items)
                if length(pickable) >= 2 then 1 else 0
            }
            example pick
                | "nothing filed" : ([], []) -> 0
            """;

    /**
     * A list the rules make hold several, and the rule left to compose a row for is fewer than two
     * filed: every element counted is a count of several, so none of them is, and the map is made
     * to hold none of their keys.
     */
    private static final String FEWER_OF_SEVERAL = """
            module p
            import List ( filterMap, length )
            data Keys = List<String>
                invariant several = List.length(value) >= 2
            behavior pick : (ks: Keys, shelf: Map<String, String>) -> Int
            let pick (ks, shelf) = {
                let pickable = filterMap(k -> Map.get(k, shelf), ks.value)
                if length(pickable) >= 2 then 1 else 0
            }
            example pick
                | "filed" : (Keys(["a", "b"]), [("a", "x"), ("b", "x")]) -> 1
            """;

    private static final List<String> NONE_FILED = List.of("Keys([\"x\", \"x\"])", "[]");

    /** Each form, with the row composed for the rule where at least two are filed. */
    private static final Map<String, List<String>> COMPOSED = Map.of(
            ITSELF, List.of("[\"x\", \"x\"]", "[(\"x\", \"x\")]"),
            FIELD, List.of("[Item { sku = \"x\", q = 0 }, Item { sku = \"x\", q = 0 }]",
                    "[(\"x\", \"x\")]"));

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

    @Test
    void eachFormIsComposedWithAKeyForEachElementCounted() {
        COMPOSED.forEach((model, expected) -> assertEquals(List.of(expected),
                composedForTheRules(measured(model)), model));
    }

    /**
     * And the points of the line the count is held against: a row at the count, one below it, and
     * one inside the region above, each with as many filed as the point asks.
     */
    @Test
    void everyPointOfTheLineOnTheCountIsComposed() {
        COMPOSED.keySet().forEach(model -> {
            String report = report(measured(model));

            assertFalse(report.contains("nothing could show a row can be written"),
                    () -> report);
        });
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

    /**
     * A list made to hold several, at a count of fewer than two: none of its elements is filed,
     * and the row answered as nothing filed takes the rule — answered as filed, it is refused.
     */
    @Test
    void aListMadeToHoldSeveralIsComposedWithNoneFiledAtACountBelowIt() {
        assertEquals(List.of(NONE_FILED), composedForTheRules(measured(FEWER_OF_SEVERAL)));

        Compilation answered = measured(FEWER_OF_SEVERAL + "    | \"none\" : ("
                + String.join(", ", NONE_FILED) + ") -> 0\n");
        assertEquals(List.of(), errors(answered));
        assertFalse(report(answered).contains("no row takes a decision rule"),
                () -> report(answered));
        assertFalse(errors(measured(FEWER_OF_SEVERAL + "    | \"none\" : ("
                + String.join(", ", NONE_FILED) + ") -> 1\n")).isEmpty());
    }

    /** The control: the same rows answered as fewer than two filed are refused. */
    @Test
    void theSameRowsAnsweredAsFewerFiledAreRefused() {
        COMPOSED.forEach((model, expected) -> assertFalse(errors(measured(model
                + "    | \"filed\" : (" + String.join(", ", expected) + ") -> 0\n")).isEmpty(),
                model));
    }
}
