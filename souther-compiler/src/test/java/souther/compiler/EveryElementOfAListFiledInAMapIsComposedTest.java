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
 * A row where every element of a list is filed in a map is composed, and the map is made to hold
 * a key for each element the list holds — none where it holds none.
 *
 * <p>Said as the statement it is: for every element of {@code ks}, some entry of {@code shelf}
 * keyed by it. A list holding nothing meets it whatever the map holds, so nothing makes the map
 * hold an entry for the list's sake; a list the rules make hold several meets it only with an
 * entry for each, and the map is built holding them.
 */
class EveryElementOfAListFiledInAMapIsComposedTest {

    private static final String EVERY = """
            module p
            behavior pick : (ks: List<String>, shelf: Map<String, String>) -> Int
            let pick (ks, shelf) =
                if List.all(k -> match Map.get(k, shelf) with
                        | Some v -> true
                        | None -> false, ks) then 1 else 0
            example pick
                | "a" : (["a"], []) -> 0
            """;

    /** A list the rules make hold several, so the statement is met only with each filed. */
    private static final String SEVERAL = """
            module p
            data Keys = List<String>
                invariant several = List.length(value) >= 2
            behavior pick : (ks: Keys, shelf: Map<String, String>) -> Int
            let pick (ks, shelf) =
                if List.all(k -> match Map.get(k, shelf) with
                        | Some v -> true
                        | None -> false, ks.value) then 1 else 0
            example pick
                | "a" : (Keys(["a", "b"]), []) -> 0
            """;

    /**
     * A list the rules make hold several no two of which are equal, so the map is made to hold an
     * entry under each.
     */
    private static final String SEVERAL_APART = """
            module p
            data Keys = List<String>
                invariant several = List.length(value) >= 2
                invariant apart = List.allDistinctBy(k -> k, value)
            behavior pick : (ks: Keys, shelf: Map<String, String>) -> Int
            let pick (ks, shelf) =
                if List.all(k -> match Map.get(k, shelf) with
                        | Some v -> true
                        | None -> false, ks.value) then 1 else 0
            example pick
                | "a" : (Keys(["a", "b"]), []) -> 0
            """;

    /**
     * A map the rules keep empty. The statement is met by a list holding nothing, so the map's
     * holding none is no refusal of the model's.
     */
    private static final String SHELF_EMPTY = """
            module p
            data Shelf = Map<String, String>
                invariant none = Map.size(value) <= 0
            behavior pick : (ks: List<String>, shelf: Shelf) -> Int
            let pick (ks, shelf) =
                if List.all(k -> match Map.get(k, shelf.value) with
                        | Some v -> true
                        | None -> false, ks) then 1 else 0
            example pick
                | "a" : (["a"], Shelf([])) -> 0
            """;

    /**
     * Every element of a list the rules make hold one holding a value of another parameter in a
     * list inside it: the inner list is written in each element the plan builds, so it is asked
     * of the plan as it is, and each element's tags hold the value.
     */
    private static final String INSIDE_EACH = """
            module p
            data Item = { tags: List<String> }
            data Items = List<Item>
                invariant some = List.length(value) >= 1
            behavior pick : (items: Items, k: String) -> Int
            let pick (items, k) =
                if List.all(i -> List.contains(k, i.tags), items.value) then 1 else 0
            example pick
                | "a" : (Items([Item { tags = [] }]), "a") -> 0
            """;

    /** The same with some element holding the value, which the list then holds one for. */
    private static final String INSIDE_SOME = INSIDE_EACH.replace("List.all(", "List.any(");

    /** Each form, with the row composed for the rule where every element is filed. */
    private static final Map<String, List<String>> COMPOSED = Map.of(
            EVERY, List.of("[]", "[]"),
            SEVERAL, List.of("Keys([\"x\", \"x\"])", "[(\"x\", \"x\")]"),
            SEVERAL_APART, List.of("Keys([\"x\", \"xx\"])",
                    "[(\"x\", \"x\"), (\"xx\", \"x\")]"),
            SHELF_EMPTY, List.of("[]", "Shelf([])"),
            INSIDE_EACH, List.of("Items([Item { tags = [\"x\"] }])", "\"x\""),
            INSIDE_SOME, List.of("Items([Item { tags = [\"x\"] }])", "\"x\""));

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
    void eachFormIsComposedWithAKeyForEachElementTheListHolds() {
        COMPOSED.forEach((model, expected) -> assertEquals(List.of(expected),
                composedForTheRules(measured(model)), model));
    }

    /**
     * The rows composed, put back as examples, take the rule they were composed for: the model
     * answers each as every element filed, and no rule is left that no row takes.
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

    /** The control: the same rows answered as not every element filed are refused. */
    @Test
    void theSameRowsAnsweredAsNotEveryElementFiledAreRefused() {
        COMPOSED.forEach((model, expected) -> assertFalse(errors(measured(model
                + "    | \"filed\" : (" + String.join(", ", expected) + ") -> 0\n")).isEmpty(),
                model));
    }
}
