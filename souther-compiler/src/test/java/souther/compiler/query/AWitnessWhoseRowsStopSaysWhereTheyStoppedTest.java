package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.SourceRendering;
import souther.compiler.execute.RunStop;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meta.ModulePath;
import souther.compiler.partition.CountWitnesses;
import souther.compiler.partition.WhereARunStopped;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where the rows a search for a witness of a count tried meet the statement both ways and every run
 * of the behavior on them stops, the search says where the runs stopped, and so does what the
 * relation the witness was for leaves its place: the report names the rule that refused the runs
 * beside the word for the place, and the document writes it under the entry for that place.
 *
 * <p>The model counts the deals whose currency is a key of the table and compares the count with
 * how many deals there are. A witness is two deals beside one table, one currency in it and one not;
 * the {@code ensures} refuses every answer counting two deals beside a table of five entries or
 * fewer, so every run on such a row stops there. Without the {@code ensures} the same search finds the witness and
 * no run stops.
 */
class AWitnessWhoseRowsStopSaysWhereTheyStoppedTest {

    private static final String ENSURES =
            "    ensures small = value.n < 2 || Map.size(rates) > 5";

    private static String model(String ensures) {
        return """
                module demo

                data CurrencyCode = String
                    invariant String.matches("[A-Z]{3}", value)

                data ConversionRate = Decimal
                    invariant value > 0.0m

                data Deal = { currency: CurrencyCode, amount: Decimal }

                data Tally = { ok: Bool, n: Int }

                let yen = Map.fromList([ (CurrencyCode("JPY"), ConversionRate(1.0m)) ])

                behavior forecast : (deals: List<Deal>, rates: Map<CurrencyCode, ConversionRate>) -> Tally
                    constructs Tally
                %s

                let forecast (deals, rates) = {
                    let kept = List.filterMap(d -> Map.get(d.currency, rates), deals)
                    guard List.length(kept) == List.length(deals) else Tally { ok = false, n = List.length(deals) }
                    Tally { ok = true, n = List.length(deals) }
                }

                example forecast
                    | "none" : ([], yen) -> Tally { ok = true, n = 0 }
                    | "kept" : ([ Deal { currency = CurrencyCode("JPY"), amount = 1.0m } ], yen) -> Tally { ok = true, n = 1 }
                    | "dropped" : ([ Deal { currency = CurrencyCode("AAA"), amount = 1.0m } ], yen) -> Tally { ok = false, n = 1 }
                """.formatted(ensures);
    }

    private static final TermPath DEALS = TermPath.of("deals");

    private static final TermPath RATES = TermPath.of("rates");

    /** How many deals have a currency some key of the table is. */
    private static final Quantity.HowManyMeet COUNT = new Quantity.HowManyMeet(
            new DecisionSubject.AnInput(DEALS),
            new Proposition.Some(new DecisionSubject.AnInput(RATES),
                    new Proposition.SameValue(new DecisionSubject.AnInput(RATES.key()),
                            new DecisionSubject.AnInput(DEALS.element().then("currency")), true),
                    true));

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** Where the runs stopped, as every entry of the document that says so writes it. */
    private static final String ENSURES_STOP = """
            [{"at": "an_ensures", "rule": "ensures forecast (small)", "module": "demo",
              "declaredIn": "demo"}]""";

    @Test
    void theSearchSaysWhereTheRunsOfTheRowsItTriedStopped() {
        Compilation compilation = compiled(model(ENSURES));
        CountWitnesses.Sought sought = sought(compilation);

        assertEquals(Optional.empty(), sought.found());
        assertEquals(Set.of(), sought.stoppedAt());
        assertEquals(Set.of(new WhereARunStopped(
                        new RunStop.AtAnEnsures("demo", "forecast", Optional.of("small")),
                        Optional.of(compilation.sourceIdOf("demo")))),
                sought.runsStopped());
    }

    @Test
    void theReportNamesTheEnsuresBesideTheWordForThePlace() {
        Compilation compilation = compiled(model(ENSURES));
        String report = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));

        assertEquals(List.of("      · not read: comparison@21:29 — what it states was read, and it"
                        + " relates the value here to another value not shown to reach every"
                        + " value here, so which values here settle it on their own is not worked"
                        + " out, and the runs stopped at the answer, where ensures forecast"
                        + " (small) did not hold, about `List.length(deals)`"),
                report.lines().filter(line -> line.contains("not read: comparison@")).toList(),
                report);
        // And the question the same reason leaves standing, under each measure that reads it.
        String standing = "      · not accounted for: comparison@21:29 — what this rule states"
                + " about List.length(deals): what it states was read, and it relates the value"
                + " here to another value not shown to reach every value here, so which values"
                + " here settle it on their own is not worked out, and the runs stopped at the"
                + " answer, where ensures forecast (small) did not hold";
        assertEquals(List.of(standing, standing), report.lines()
                .filter(line -> line.contains("not accounted for: comparison@")).toList(), report);
    }

    @Test
    void theDocumentWritesWhereTheRunsStoppedUnderWhatTheQuestionStandsOn() {
        Compilation compilation = compiled(model(ENSURES));
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);

        List<JsonNode> stopped = new ArrayList<>();
        for (JsonNode module : document.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode question : behavior.path("partition").path("unanswered")) {
                    for (JsonNode standsOn : question.path("stopped")) {
                        if (standsOn.has("runsStopped")) {
                            assertEquals("relation_not_shown_to_reach_every_value",
                                    standsOn.path("reason").asString(), standsOn.toString());
                            stopped.add(standsOn.path("runsStopped"));
                        }
                    }
                }
            }
        }
        assertEquals(List.of(JSON.readTree(ENSURES_STOP)), stopped);
    }

    @Test
    void theDocumentWritesWhereTheRunsStoppedUnderTheEntryForThePlace() {
        Compilation compilation = compiled(model(ENSURES));
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);

        List<JsonNode> stopped = new ArrayList<>();
        for (JsonNode each : notRead(document)) {
            if (each.has("runsStopped")) {
                assertEquals("List.length(deals)", each.path("position").asString(),
                        each.toString());
                assertEquals("relation_not_shown_to_reach_every_value",
                        each.path("reason").asString(), each.toString());
                stopped.add(each.path("runsStopped"));
            }
        }
        assertEquals(List.of(JSON.readTree(ENSURES_STOP)), stopped);
    }

    /** The control: without the ensures the same search finds its witness, and no run stopped. */
    @Test
    void withoutTheEnsuresTheWitnessIsFoundAndNoRunStopped() {
        Compilation compilation = compiled(model(""));
        CountWitnesses.Sought sought = sought(compilation);

        assertTrue(sought.found().isPresent(), sought.toString());
        assertEquals(Set.of(), sought.runsStopped());
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        assertEquals(List.of(), notRead(document).stream()
                .filter(each -> each.has("runsStopped")).toList());
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");
        return compilation;
    }

    /** What the search for a witness of {@link #COUNT} came to, at a run going through the
     *  comparison the body writes. */
    private static CountWitnesses.Sought sought(Compilation compilation) {
        Set<ConditionOutcomeSite> reaching = new HashSet<>();
        compilation.db().ask(new Bodies.Observable("demo")).value().plan().sites().forEach(site -> {
            if (site instanceof CoverageSites.ComparisonSite compared
                    && compared.body().equals("forecast")) {
                reaching.add(compared.index());
            }
        });
        return compilation.db().ask(new Adequacy.WitnessOfACount("demo", "forecast", COUNT,
                reaching)).value();
    }

    /** Every entry of every behavior's {@code notRead}. */
    private static List<JsonNode> notRead(JsonNode document) {
        List<JsonNode> out = new ArrayList<>();
        for (JsonNode module : document.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                behavior.path("partition").path("notRead").forEach(out::add);
            }
        }
        return out;
    }
}
