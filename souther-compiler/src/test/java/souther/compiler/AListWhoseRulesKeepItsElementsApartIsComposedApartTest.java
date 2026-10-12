package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Generator;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A list whose rules say no two of its elements come to one answer of a closure is composed with
 * its elements apart at what that closure answers, wherever a list of it is built.
 *
 * <p>Said as the rule it is: {@code List.allDistinctBy(k -> k, value)} keeps the elements apart as
 * values, and {@code List.allDistinctBy(l -> l.sku, value)} keeps them apart at their {@code sku}.
 * A list built around an element some element is asked of, around every element, to a size the
 * declaration's own line is drawn at, and to a count of the elements meeting a statement is each
 * built that way, and a row put back with what was composed is one the decoder takes.
 */
class AListWhoseRulesKeepItsElementsApartIsComposedApartTest {

    /** Some element filed in a map, of a list the rules make hold several apart. */
    private static final String SOME = """
            module p
            data Keys = List<String>
                invariant several = List.length(value) >= 2
                invariant apart = List.allDistinctBy(k -> k, value)
            behavior pick : (ks: Keys, shelf: Map<String, String>) -> Int
            let pick (ks, shelf) =
                if List.any(k -> match Map.get(k, shelf) with
                        | Some v -> true
                        | None -> false, ks.value) then 1 else 0
            example pick
                | "a" : (Keys(["a", "b"]), []) -> 0
            """;

    /** Every element filed, of the same list. */
    private static final String EVERY = SOME.replace("List.any(", "List.all(");

    /** Some element of a list of records apart at a field, filed by that field. */
    private static final String SOME_BY_FIELD = """
            module p
            data Line = { sku: String, q: Int }
            data Lines = List<Line>
                invariant several = List.length(value) >= 2
                invariant apart = List.allDistinctBy(l -> l.sku, value)
            behavior pick : (ls: Lines, shelf: Map<String, String>) -> Int
            let pick (ls, shelf) =
                if List.any(l -> match Map.get(l.sku, shelf) with
                        | Some v -> true
                        | None -> false, ls.value) then 1 else 0
            example pick
                | "a" : (Lines([Line { sku = "a", q = 0 }, Line { sku = "b", q = 0 }]), []) -> 0
            """;

    /** The same, kept apart as records as well: apart at the field is apart as records. */
    private static final String SOME_BY_FIELD_AND_WHOLE = SOME_BY_FIELD.replace(
            "    invariant apart =",
            "    invariant whole = List.allDistinctBy(l -> l, value)\n    invariant apart =");

    /** The same, kept apart at a second field besides. */
    private static final String SOME_BY_TWO_FIELDS = SOME_BY_FIELD
            .replace("{ sku: String, q: Int }", "{ sku: String, serial: String, q: Int }")
            .replace("    invariant apart =",
                    "    invariant serials = List.allDistinctBy(l -> l.serial, value)\n"
                            + "    invariant apart =")
            .replace("sku = \"a\", q = 0", "sku = \"a\", serial = \"s\", q = 0")
            .replace("sku = \"b\", q = 0", "sku = \"b\", serial = \"t\", q = 0");

    /** So many elements over a line, of a list of numbers the rules keep apart. */
    private static final String COUNTED = """
            module p
            data Keys = List<Int>
                invariant several = List.length(value) >= 3
                invariant apart = List.allDistinctBy(k -> k, value)
            behavior pick : (ks: Keys) -> Int
            let pick (ks) =
                if List.length(List.filter(k -> k > 5, ks.value)) >= 2 then 1 else 0
            example pick
                | "a" : (Keys([1, 2, 3])) -> 0
            """;

    /** So many elements filed in a map, where what is counted is handed on to the map. */
    private static final String HANDED_ON = """
            module p
            import List ( filterMap, length )
            data Keys = List<String>
                invariant several = List.length(value) >= 2
                invariant apart = List.allDistinctBy(k -> k, value)
            behavior pick : (ks: Keys, shelf: Map<String, String>) -> Int
            let pick (ks, shelf) = {
                let pickable = filterMap(k -> Map.get(k, shelf), ks.value)
                if length(pickable) >= 2 then 1 else 0
            }
            example pick
                | "filed" : (Keys(["a", "b"]), [("a", "x"), ("b", "x")]) -> 1
            """;

    /** Each form, with the row composed for the decision rule no example takes and what the model
     *  answers it. */
    private static final Map<String, Composed> COMPOSED = Map.of(
            SOME, new Composed(List.of("Keys([\"x\", \"xx\"])", "[(\"x\", \"x\")]"), 1),
            EVERY, new Composed(List.of("Keys([\"x\", \"xx\"])",
                    "[(\"x\", \"x\"), (\"xx\", \"x\")]"), 1),
            SOME_BY_FIELD, new Composed(List.of(
                    "Lines([Line { sku = \"x\", q = 0 }, Line { sku = \"xx\", q = 0 }])",
                    "[(\"x\", \"x\")]"), 1),
            SOME_BY_FIELD_AND_WHOLE, new Composed(List.of(
                    "Lines([Line { sku = \"x\", q = 0 }, Line { sku = \"xx\", q = 0 }])",
                    "[(\"x\", \"x\")]"), 1),
            SOME_BY_TWO_FIELDS, new Composed(List.of(
                    "Lines([Line { sku = \"x\", serial = \"x\", q = 0 },"
                            + " Line { sku = \"xx\", serial = \"xx\", q = 0 }])",
                    "[(\"x\", \"x\")]"), 1),
            COUNTED, new Composed(List.of("Keys([4, 6, 7])"), 1),
            HANDED_ON, new Composed(List.of("Keys([\"x\", \"xx\"])", "[]"), 0));

    private record Composed(List<String> inputs, int answer) {}

    /** The runs each form keeps its elements apart at, as the test reads a composed list. */
    private static final Map<String, List<List<String>>> APART_AT = Map.of(
            SOME, List.of(List.of()),
            EVERY, List.of(List.of()),
            SOME_BY_FIELD, List.of(List.of("sku")),
            SOME_BY_FIELD_AND_WHOLE, List.of(List.of("sku")),
            SOME_BY_TWO_FIELDS, List.of(List.of("sku"), List.of("serial")),
            COUNTED, List.of(List.of()),
            HANDED_ON, List.of(List.of()));

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

    private static List<GenerationOutcome> outcomes(Compilation compilation) {
        return Adequacy.generatedOf(compilation.db(), compilation.modules().get(0)).get("pick")
                .generation().stream().map(each -> each.outcome()).toList();
    }

    /** The rows composed for the decision rules no row takes, each as the texts of its inputs. */
    private static List<List<String>> composedForTheRules(Compilation compilation) {
        List<List<String>> out = new ArrayList<>();
        Adequacy.generatedOf(compilation.db(), compilation.modules().get(0)).get("pick")
                .generation().stream()
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

    /** The elements of the list {@code value} writes, under whatever names it wears. */
    private static List<Hir.Expr> elementsOf(Hir.Expr value) {
        Hir.Expr at = value;
        while (at instanceof Hir.Apply applied && applied.args().size() == 1) {
            at = applied.args().getFirst();
        }
        return at instanceof Hir.ListLit list ? list.elements() : null;
    }

    /** What {@code element} holds at the end of {@code run}, under whatever names it wears. */
    private static Hir.Expr at(Hir.Expr element, List<String> run) {
        Hir.Expr at = element;
        for (String field : run) {
            while (at instanceof Hir.Apply applied && applied.args().size() == 1) {
                at = applied.args().getFirst();
            }
            Hir.NewData record = assertInstanceOf(Hir.NewData.class, at);
            at = record.inits().stream().filter(each -> each.name().equals(field)).findFirst()
                    .orElseThrow().value();
        }
        return at;
    }

    @Test
    void eachFormIsComposedWithItsElementsApart() {
        COMPOSED.forEach((model, expected) -> assertEquals(List.of(expected.inputs()),
                composedForTheRules(measured(model)), model));
    }

    /**
     * Every list composed for anything at all — a rule, a line the declaration draws, a class —
     * holds its elements apart at every run its rules keep them apart at.
     */
    @Test
    void everyListComposedHoldsItsElementsApart() {
        APART_AT.forEach((model, runs) -> {
            int lists = 0;
            for (GenerationOutcome outcome : outcomes(measured(model))) {
                if (!(outcome instanceof GenerationOutcome.Generated made)) {
                    continue;
                }
                for (var row : made.candidates()) {
                    List<Hir.Expr> elements = elementsOf(row.inputs().getFirst().value());
                    lists++;
                    for (List<String> run : runs) {
                        Set<Hir.Expr> seen = new HashSet<>();
                        for (Hir.Expr each : elements) {
                            assertTrue(seen.add(at(each, run)), () -> model + " composed "
                                    + row.inputs().getFirst().text() + ", repeated at " + run);
                        }
                    }
                }
            }
            assertTrue(lists > 0, model);
        });
    }

    /**
     * The rows composed, put back as examples, take the rule they were composed for: the decoder
     * takes the list, and no rule is left that no row takes.
     */
    @Test
    void theRowsComposedTakeTheRuleTheyWereComposedFor() {
        COMPOSED.forEach((model, expected) -> {
            Compilation answered = measured(model + "    | \"composed\" : ("
                    + String.join(", ", expected.inputs()) + ") -> " + expected.answer() + "\n");

            assertEquals(List.of(), errors(answered), model);
            assertFalse(report(answered).contains("no row takes a decision rule"),
                    () -> report(answered));
        });
    }

    /**
     * A list of booleans the rules keep apart and make hold three is a list no value is, and
     * nothing here proves it: the values put beside each other ran out, which is this compiler
     * not finding a third and not the model refusing one. So nothing composed for it is said as
     * what the rules leave.
     */
    @Test
    void aListTheElementsRunOutForIsNoProofTheRulesLeaveNone() {
        String bools = """
                module p
                data Flags = List<Bool>
                    invariant several = List.length(value) >= 3
                    invariant apart = List.allDistinctBy(k -> k, value)
                behavior pick : (fs: Flags) -> Int
                let pick (fs) =
                    if List.any(k -> k, fs.value) then 1 else 0
                example pick
                    | "a" : (Flags([true, false, true])) -> 0
                """;
        List<Generator.UnresolvedCombination.Reason> said = new ArrayList<>();
        for (GenerationOutcome outcome : outcomes(measured(bools))) {
            assertFalse(outcome instanceof GenerationOutcome.Generated, outcome::toString);
            if (outcome instanceof GenerationOutcome.CannotGenerate(List<CameToNothing> why)) {
                why.forEach(each -> said.add(each.why().reason()));
            }
        }
        assertFalse(said.isEmpty());
        assertFalse(said.contains(
                Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE),
                said::toString);
    }

    /**
     * The rule is said to be one about how the elements stand to each other, and not one written in
     * a form this compiler does not read — and still as a rule the position's values were not
     * worked out under, since a list saying one element twice is among what the position is taken
     * to hold. A closure this does not read is a form it does not read, which is the control.
     */
    @Test
    void theRuleIsSaidToRelateTheElementsWhereItsClosureIsRead() {
        String unread = "not accounted for: invariant Keys (apart) — which values may stand at ks:";
        COMPOSED.keySet().stream().filter(model -> model.contains("Keys")).forEach(model -> {
            String report = report(measured(model));
            assertTrue(report.contains(unread + " it says how the elements here stand to each"
                    + " other, and which containers it leaves is not worked out"), report);
            assertFalse(report.contains("written in a form this compiler does not read"), report);
        });
        String report = report(measured(SOME.replace("List.allDistinctBy(k -> k, value)",
                "List.allDistinctBy(k -> String.length(k), value)")));
        assertTrue(report.contains(unread + " written in a form this compiler does not read"),
                report);
    }

    /**
     * Nothing the declaration's own lines are drawn at is left as a point no value tried could be
     * written at: what was refused there was a list saying one element twice.
     */
    @Test
    void noPointOfTheDeclarationIsLeftAsEveryValueRefused() {
        COMPOSED.keySet().forEach(model -> {
            String report = report(measured(model));
            assertFalse(report.contains("every value tried at"), () -> model + report);
        });
    }
}
