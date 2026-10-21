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
 * the element and the answer together and none of them is a number of the input alone. And of the
 * element asked two comparisons with the answer, either or both, and one beside a rule of the
 * input alone: each way of the quantifier, held and denied, asks the row something else of the
 * element. And of a helper met at two calls, only one of which is about the answer, and of the
 * model the defect was reported with.
 */
class AComparisonOfAnAnswerWithAnElementOfTheInputIsComposedWithThatElementTest {

    private static final String HEAD = """
            module p
            data Amount = Decimal
                invariant value >= 0.0m
            data Quota = Decimal
                invariant value > 0.0m
            data Span = { low: Amount, high: Amount }
            data Forecast = { byPeriod: Map<String, Amount>, list: List<Amount>, spans: List<Span> }
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
                    | "nothing filed" : (0, Forecast { byPeriod = [], list = [], spans = [] }, "x")
                        with quotaFor = Quota(1m) -> 0
                """.formatted(condition);
    }

    private static final String SOME_ELEMENT = HEAD + """
                {
                    let quota = quotaFor(owner, period)
                    if List.any(a -> a.value >= quota.value, forecast.list) then 1 else 2
                }
            """;

    /** Some element of a list held against the answer at two of its numbers, joined by
     *  {@code JOIN}. */
    private static String someSpan(String join) {
        return HEAD + """
                    {
                        let quota = quotaFor(owner, period)
                        if List.any(s -> s.low.value >= quota.value %s s.high.value >= quota.value,
                                forecast.spans) then 1 else 2
                    }
                """.formatted(join);
    }

    /**
     * Some element of a list meeting a rule of the input beside the comparison with the answer:
     * the element the answer is composed for has to meet that rule as well, and where no element
     * may meet both, one that fails the rule is no element the answer was composed against.
     */
    private static final String BESIDE_A_RULE_OF_THE_INPUT = HEAD + """
                {
                    let quota = quotaFor(owner, period)
                    if List.any(s -> s.low.value > 0.0m && s.high.value >= quota.value,
                            forecast.spans) then 1 else 2
                }
            """;

    /**
     * A helper whose comparison is met at two calls: one of the input alone, one of the entry a
     * lookup selects against the answer. The two are one comparison written once, and two
     * conditions on the way to the rule — the second restated with its values in leaves the first
     * as it was.
     */
    private static final String ONE_HELPER_TWO_CALLS = """
            module p
            data Amount = Decimal
                invariant value >= 0.0m
            data Quota = Decimal
                invariant value > 0.0m
            data Forecast = { byPeriod: Map<String, Amount>, floor: Amount }
            behavior quotaFor : (owner: Int, period: String) -> Quota
            behavior reaches : (owner: Int, forecast: Forecast, period: String) -> Int
                depends on quotaFor
            let atLeast (a: Decimal, b: Decimal) = a >= b
            let reaches (owner, forecast, period, quotaFor) =
                match Map.get(period, forecast.byPeriod) with
                    | None -> 0
                    | Some got -> {
                        let quota = quotaFor(owner, period)
                        if atLeast(forecast.floor.value, 5.0m) && atLeast(got.value, quota.value)
                        then 1 else 2
                    }
            example reaches
                | "nothing filed" : (0, Forecast { byPeriod = [], floor = Amount(0m) }, "x")
                    with quotaFor = Quota(1m) -> 0
                | "under the floor" : (0, Forecast { byPeriod = [("x", Amount(0m))],
                    floor = Amount(0m) }, "x") with quotaFor = Quota(1m) -> 2
            """;

    /** The model the issue was reported with, which answers a record built of both values. */
    private static final String AS_REPORTED = """
            module f0
            data Amount = Decimal
                invariant value >= 0.0m
            data Quota = Decimal
                invariant value > 0.0m
            data Forecast = { byPeriod: Map<String, Amount> }
            data Short = { gap: Decimal }
            behavior quotaFor : (owner: Int, period: String) -> Quota
            behavior att : (owner: Int, forecast: Forecast, period: String) -> Bool | Short
                depends on quotaFor
            let att (owner, forecast, period, quotaFor) =
                match Map.get(period, forecast.byPeriod) with
                    | None -> false
                    | Some got -> {
                        let quota = quotaFor(owner, period)
                        if Decimal.compare(got.value, quota.value) >= 0 then true
                        else Short { gap = Decimal.subtract(quota.value, got.value) }
                    }
            example att
                | "nothing filed" : (0, Forecast { byPeriod = [] }, "x")
                    with quotaFor = Quota(1m) -> false
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
            row("Forecast { byPeriod = [(\"x\", Amount(1m))], list = [], spans = [] }", "1"),
            row("Forecast { byPeriod = [(\"x\", Amount(0m))], list = [], spans = [] }", "2"));

    /**
     * The behavior a form's rows are composed for, the rows, and what another rule of it answers
     * — which the control answers a row with.
     */
    private record Composed(String behavior, List<Row> rows, String anotherRuleAnswers) {

        /** What the control answers the row at {@code at} with: what another of the rows
         *  answers, or another rule where there is no other row. */
        String answeredOtherwise(int at) {
            return rows.size() > 1 ? rows.get((at + 1) % rows.size()).answers()
                    : anotherRuleAnswers;
        }
    }

    /** Each form, with the rows composed for the rules no row takes. */
    private static final Map<String, Composed> COMPOSED = new LinkedHashMap<>();

    private static void reaching(String model, Row... rows) {
        COMPOSED.put(model, new Composed("reaches", List.of(rows), "2"));
    }

    static {
        reaching(lookedUp("got.value >= quota.value"), LOOKED_UP_ROWS.toArray(Row[]::new));
        reaching(lookedUp("Decimal.compare(got.value, quota.value) >= 0"),
                LOOKED_UP_ROWS.toArray(Row[]::new));
        reaching(SOME_ELEMENT,
                row("Forecast { byPeriod = [], list = [Amount(1m)], spans = [] }", "1"),
                row("Forecast { byPeriod = [], list = [Amount(0m)], spans = [] }", "2"));
        reaching(someSpan("||"),
                row("Forecast { byPeriod = [], list = [], spans = [Span { low = Amount(1m),"
                        + " high = Amount(0m) }] }", "1"),
                row("Forecast { byPeriod = [], list = [], spans = [Span { low = Amount(0m),"
                        + " high = Amount(0m) }] }", "2"));
        reaching(someSpan("&&"),
                row("Forecast { byPeriod = [], list = [], spans = [Span { low = Amount(1m),"
                        + " high = Amount(1m) }] }", "1"),
                row("Forecast { byPeriod = [], list = [], spans = [Span { low = Amount(0m),"
                        + " high = Amount(0m) }] }", "2"));
        reaching(BESIDE_A_RULE_OF_THE_INPUT,
                row("Forecast { byPeriod = [], list = [], spans = [Span { low = Amount(1m),"
                        + " high = Amount(1m) }] }", "1"),
                row("Forecast { byPeriod = [], list = [], spans = [Span { low = Amount(0m),"
                        + " high = Amount(0m) }] }", "2"));
        reaching(ONE_HELPER_TWO_CALLS,
                row("Forecast { byPeriod = [(\"x\", Amount(1m))], floor = Amount(5m) }", "1"));
        COMPOSED.put(AS_REPORTED, new Composed("att", List.of(
                row("Forecast { byPeriod = [(\"x\", Amount(1m))] }", "true"),
                row("Forecast { byPeriod = [(\"x\", Amount(0m))] }", "Short { gap = 1m }")),
                "false"));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /** Compiled and run and not measured, for a question about what its rows answer: a row that
     *  does not hold is refused by running it, and nothing the measurement finds is read. */
    private static Compilation unmeasured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
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
    private static List<List<String>> composedForTheRules(Compilation compilation,
                                                          String behavior) {
        Adequacy.Filling filling = Adequacy.generatedOf(compilation.db(),
                compilation.modules().get(0)).get(behavior);
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

    /**
     * {@code model} with the rows written as examples of it — each answered as the model does, or
     * as another rule is ({@link Composed#answeredOtherwise}).
     */
    private static String withRows(String model, Composed composed,
                                   boolean answeredAsTheModelDoes) {
        List<Row> rows = composed.rows();
        StringBuilder out = new StringBuilder(model);
        if (!model.contains("example " + composed.behavior())) {
            out.append("example ").append(composed.behavior()).append('\n');
        }
        for (int at = 0; at < rows.size(); at++) {
            Row row = rows.get(at);
            String answered = answeredAsTheModelDoes ? row.answers()
                    : composed.answeredOtherwise(at);
            out.append("    | \"composed ").append(at).append("\" : (").append(row.input())
                    .append(") with quotaFor = ").append(row.quota()).append(" -> ")
                    .append(answered).append('\n');
        }
        return out.toString();
    }

    /** The element is written holding the value the answer was composed for. */
    @Test
    void eachFormIsComposedWithTheElementTheAnswerIsComparedWith() {
        COMPOSED.forEach((model, composed) -> assertEquals(
                composed.rows().stream().map(Row::written).toList(),
                composedForTheRules(measured(model), composed.behavior()), model));
    }

    /**
     * The rows composed, put back as examples, take the rule they were composed for: the model
     * answers each as the rule says, and no rule is left that no row takes.
     */
    @Test
    void theRowsComposedTakeTheRuleTheyWereComposedFor() {
        COMPOSED.forEach((model, composed) -> {
            Compilation answered = measured(withRows(model, composed, true));

            assertEquals(List.of(), errors(answered), model);
            assertFalse(report(answered).contains("no row takes a decision rule"),
                    () -> report(answered));
        });
    }

    /** The control: the same rows answered as another of them is are refused. */
    @Test
    void theSameRowsAnsweredAsAnotherRuleAreRefused() {
        COMPOSED.forEach((model, composed) -> assertFalse(
                errors(unmeasured(withRows(model, composed, false))).isEmpty(), model));
    }
}
