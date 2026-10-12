package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.StoodInAnswer;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A row for a rule that compares what a dependency answered with an element of the input is
 * composed with that element, and the answer is composed for the value the element holds.
 *
 * <p>Said as the statement it is: the entry a lookup selects, or some element of a list, holding a
 * value at least the quota the dependency answers. The answer and the element are one statement
 * about the pair, so the element's value is put at a number first, the answer is composed for that
 * number, and the row is held to it on the element the statement is about — the entry under the
 * key, not some other entry, and an element of the list the list is built holding.
 *
 * <p>Asked of the forms the comparison takes — through the value a lookup selects, spelled directly
 * and through the order an operation answers, and of some element of a list — because each states
 * the element and the answer together and none of them is a number of the input alone.
 */
class AComparisonOfAnAnswerWithAnElementOfTheInputIsComposedWithThatElementTest {

    private static final String HEAD = """
            module p
            data Amount = Decimal
                invariant value >= 0.0m
            data Quota = Decimal
                invariant value > 0.0m
            data Forecast = { byPeriod: Map<String, Amount>, list: List<Amount> }
            behavior quotaFor : (owner: Int, period: String) -> Quota
            behavior reaches : (owner: Int, forecast: Forecast, period: String) -> Int
                depends on quotaFor
            let reaches (owner, forecast, period, quotaFor) =
            """;

    private static String lookedUp(String condition) {
        return HEAD + """
                    match Map.get(period, forecast.byPeriod) with
                        | None -> 0
                        | Some got -> {
                            let quota = quotaFor(owner, period)
                            if %s then 1 else 2
                        }
                example reaches
                    | "nothing filed" : (0, Forecast { byPeriod = [], list = [] }, "x")
                        with quotaFor = Quota(1m) -> 0
                """.formatted(condition);
    }

    private static final String SOME_ELEMENT = HEAD + """
                {
                    let quota = quotaFor(owner, period)
                    if List.any(a -> a.value >= quota.value, forecast.list) then 1 else 2
                }
            """;

    /**
     * A row: what it writes at each parameter, what it stands the dependency in with, and what the
     * model answers for it.
     */
    private record Row(List<String> inputs, String quota, String answers) {

        String input() {
            return String.join(", ", inputs);
        }

        List<String> written() {
            List<String> out = new ArrayList<>(inputs);
            out.add(quota);
            return out;
        }
    }

    private static Row row(String forecast, String answers) {
        return new Row(List.of("0", forecast, "\"x\""), "Quota(1m)", answers);
    }

    private static final List<Row> LOOKED_UP_ROWS = List.of(
            row("Forecast { byPeriod = [(\"x\", Amount(1m))], list = [] }", "1"),
            row("Forecast { byPeriod = [(\"x\", Amount(0m))], list = [] }", "2"));

    /** Each form, with the rows composed for the rules no row takes. */
    private static final Map<String, List<Row>> COMPOSED = new LinkedHashMap<>();

    static {
        COMPOSED.put(lookedUp("got.value >= quota.value"), LOOKED_UP_ROWS);
        COMPOSED.put(lookedUp("Decimal.compare(got.value, quota.value) >= 0"), LOOKED_UP_ROWS);
        COMPOSED.put(SOME_ELEMENT, List.of(
                row("Forecast { byPeriod = [], list = [Amount(1m)] }", "1"),
                row("Forecast { byPeriod = [], list = [Amount(0m)] }", "2")));
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

    private static List<String> errors(Compilation compilation) {
        return compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                .toList();
    }

    /** The rows composed for the rules no row takes, as what each writes and stands in. */
    private static List<List<String>> composedForTheRules(Compilation compilation) {
        Adequacy.Filling filling = Adequacy.generatedOf(compilation.db(),
                compilation.modules().get(0)).get("reaches");
        List<List<String>> out = new ArrayList<>();
        filling.generation().stream()
                .filter(each -> each.finding().about() instanceof About.ARuleNoRowTakes)
                .forEach(each -> {
                    GenerationOutcome.Generated made = assertInstanceOf(
                            GenerationOutcome.Generated.class, each.outcome(),
                            () -> "a row is composed for the rule: " + each.outcome());
                    made.candidates().forEach(row -> {
                        List<String> written = new ArrayList<>(
                                row.inputs().stream().map(FixtureTemplate::text).toList());
                        row.answers().forEach(stood -> written.add(
                                assertInstanceOf(StoodInAnswer.OnTheRow.class, stood)
                                        .value().text()));
                        out.add(written);
                    });
                });
        return out;
    }

    /** {@code model} with {@code rows} written as examples of it. */
    private static String withRows(String model, List<Row> rows, boolean answeredAsTheModelDoes) {
        StringBuilder out = new StringBuilder(model);
        if (!model.contains("example reaches")) {
            out.append("example reaches\n");
        }
        for (int at = 0; at < rows.size(); at++) {
            Row row = rows.get(at);
            String answered = answeredAsTheModelDoes ? row.answers()
                    : row.answers().equals("1") ? "2" : "1";
            out.append("    | \"composed ").append(at).append("\" : (").append(row.input())
                    .append(") with quotaFor = ").append(row.quota()).append(" -> ")
                    .append(answered).append('\n');
        }
        return out.toString();
    }

    /** The element is written holding the value the answer was composed for. */
    @Test
    void eachFormIsComposedWithTheElementTheAnswerIsComparedWith() {
        COMPOSED.forEach((model, expected) -> assertEquals(
                expected.stream().map(Row::written).toList(),
                composedForTheRules(measured(model)), model));
    }

    /**
     * The rows composed, put back as examples, take the rule they were composed for: the model
     * answers each as the rule says, and no rule is left that no row takes.
     */
    @Test
    void theRowsComposedTakeTheRuleTheyWereComposedFor() {
        COMPOSED.forEach((model, rows) -> {
            Compilation answered = measured(withRows(model, rows, true));

            assertEquals(List.of(), errors(answered), model);
            assertFalse(report(answered).contains("no row takes a decision rule"),
                    () -> report(answered));
        });
    }

    /** The control: the same rows answered the other way are refused. */
    @Test
    void theSameRowsAnsweredTheOtherWayAreRefused() {
        COMPOSED.forEach((model, rows) -> assertFalse(
                errors(measured(withRows(model, rows, false))).isEmpty(), model));
    }
}
