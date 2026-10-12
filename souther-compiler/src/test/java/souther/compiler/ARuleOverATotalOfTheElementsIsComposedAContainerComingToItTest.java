package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
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
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A decision rule whose condition compares what the elements of a container add up to is composed
 * a row the way a point of the same comparison is: a container whose elements come to a total the
 * condition admits, beside whatever else the way to the rule fixes.
 *
 * <p>Held by running the rows. Each row composed for a rule is put back as an example, answered
 * with what the condition works out to over the numbers the row holds — added up here, apart from
 * anything the compiler read — so a row standing short of its rule, or a total the composing got
 * wrong, is an example the model answers otherwise. And with every row put back, no rule is left
 * that no row takes.
 */
class ARuleOverATotalOfTheElementsIsComposedAContainerComingToItTest {

    /** A field of each element added up, of a list the rules make hold three. */
    private static final String A_FIELD = """
            module p
            data Line = { sku: String, q: Int }
            data Lines = List<Line>
                invariant several = List.length(value) >= 3
            behavior pick : (ls: Lines) -> Int
            let pick (ls) =
                if List.sum(List.map(l -> l.q, ls.value)) >= 10 then 1 else 0
            """;

    /** The leaves of a list of lists added up. */
    private static final String LISTS_OF_A_LIST = """
            module p
            data Posting = { q: Int }
            data Entry = { postings: List<Posting> }
            data Ledger = { entries: List<Entry> }
            behavior pick : (ledger: Ledger) -> Int
            let pick (ledger) =
                if List.sum(List.map(p -> p.q, List.flatMap(.postings, ledger.entries))) >= 10
                then 1 else 0
            """;

    /** A total held between two ends, which is one demand on it and not two. */
    private static final String BETWEEN = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>) -> Int
            let pick (ls) = {
                let t = List.sum(List.map(l -> l.q, ls))
                if t >= 10 && t <= 20 then 1 else 0
            }
            """;

    /**
     * A total added to another parameter, with the elements kept small and the other held low: the
     * two are chosen together, and the total has to be large enough that the list holds several.
     */
    private static final String BESIDE_ANOTHER = """
            module p
            data Line = { q: Int }
                invariant small = q >= 0 && q <= 2
            behavior pick : (ls: List<Line>, y: Int) -> Int
            let pick (ls, y) =
                if List.sum(List.map(l -> l.q, ls)) + y >= 10 && y <= 3 then 1 else 0
            """;

    /** What each model's condition works out to over the numbers a row holds, each parameter's
     *  whole numbers added up. */
    private static final Map<String, Function<List<Long>, Integer>> ANSWERED = Map.of(
            A_FIELD, totals -> totals.get(0) >= 10 ? 1 : 0,
            LISTS_OF_A_LIST, totals -> totals.get(0) >= 10 ? 1 : 0,
            BETWEEN, totals -> totals.get(0) >= 10 && totals.get(0) <= 20 ? 1 : 0,
            BESIDE_ANOTHER, totals -> totals.get(0) + totals.get(1) >= 10 && totals.get(1) <= 3
                    ? 1 : 0);

    @Test
    void everyRuleIsComposedARowThatTakesIt() {
        ANSWERED.forEach((model, answered) -> {
            List<String> examples = new ArrayList<>();
            Set<Integer> answers = new TreeSet<>();
            for (List<FixtureTemplate> row : composedForTheRules(measured(model))) {
                List<Long> totals = row.stream().map(each -> totalOf(each.value())).toList();
                int answer = answered.apply(totals);
                answers.add(answer);
                examples.add("    | \"composed " + examples.size() + "\" : ("
                        + String.join(", ", row.stream().map(FixtureTemplate::text).toList())
                        + ") -> " + answer);
            }
            assertEquals(Set.of(0, 1), answers,
                    () -> "a row on each side of the condition: " + examples);

            Compilation answeredBy = measured(model + "example pick\n"
                    + String.join("\n", examples) + "\n");
            assertEquals(List.of(), answeredBy.errors().stream()
                    .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                    .toList(), () -> "each row is answered as its total says: " + examples);
            assertFalse(report(answeredBy).contains("no row takes a decision rule"),
                    () -> report(answeredBy));
        });
    }

    /**
     * And none of them is a rule whose row was composed without the condition that leads to it:
     * the total is one of the numbers the row was composed against.
     */
    @Test
    void noRuleIsComposedWithoutTheTotalOnTheWayToIt() {
        for (String model : ANSWERED.keySet()) {
            String report = report(measured(model));
            assertFalse(report.contains("nothing could show a row can be written at"),
                    () -> report);
        }
    }

    /** The rows composed for the decision rules no row takes, each as its inputs. */
    private static List<List<FixtureTemplate>> composedForTheRules(Compilation compilation) {
        List<List<FixtureTemplate>> out = new ArrayList<>();
        Adequacy.generatedOf(compilation.db(), compilation.modules().get(0)).get("pick")
                .generation().stream()
                .filter(each -> each.finding().about() instanceof About.ARuleNoRowTakes)
                .forEach(each -> {
                    GenerationOutcome.Generated made = assertInstanceOf(
                            GenerationOutcome.Generated.class, each.outcome(),
                            () -> "a row is composed for the rule: " + each.outcome());
                    made.candidates().forEach(row -> out.add(row.inputs()));
                });
        assertTrue(out.size() >= 2, () -> "a row for each rule: " + out);
        return out;
    }

    /** Every whole number {@code value} writes, added up: the numbers each of these models totals
     *  are the only ones its values hold. */
    private static long totalOf(Hir.Expr value) {
        return switch (value) {
            case Hir.IntLit number -> number.value();
            case Hir.Neg negated -> -totalOf(negated.operand());
            case Hir.Apply applied -> applied.args().stream().mapToLong(each -> totalOf(each))
                    .sum();
            case Hir.ListLit list -> list.elements().stream().mapToLong(each -> totalOf(each))
                    .sum();
            case Hir.NewData record -> record.inits().stream()
                    .mapToLong(each -> totalOf(each.value())).sum();
            default -> 0;
        };
    }

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
}
