package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.check.RuleRef;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.BlockReason;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Figure;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.ReachWitnesses;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.report.AdequacyReport;
import souther.compiler.types.SourceConstructOrigin;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where the search for a row getting to a relation stopped at a figure before it had tried
 * everything, and none of the rows it tried got there, the places the relation is not shown
 * reached at every value say the figure: a run allowed more may find the row.
 *
 * <p>The relation is reached only under a base nothing the search tries holds, and the model names
 * more rates than the search tries, so the rows it tries answer without going through the relation
 * and no run stops. The sensitivity, the figures, the page and the document all say what the
 * search stopped at, as they do for a search that found no row to show a count.
 */
class AReachSearchThatStoppedAtAFigureSaysSoAtEachPlaceTest {

    /** More rates than a search tries. */
    private static final int RATES = 300;

    private static final Figure STOPPED =
            CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure();

    /** The two places the relation compares, apart from the length the other relation reads. */
    private static final List<String> PLACES = List.of("deals[*].currency", "rates.base");

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static String model() {
        StringBuilder many = new StringBuilder();
        for (int i = 0; i < RATES; i++) {
            many.append("let r").append(i).append(" = Rates { rates = Map.fromList([ (\"Z\", 0) ]),"
                    + " base = \"b").append(i).append("\" }\n");
        }
        return """
                module probe

                data Deal = { currency: String, amount: Int }
                data Rates = { rates: Map<String, Int>, base: String }
                    invariant zeroUnderZ = zeroAtZ(rates)
                data Tally = { ok: Bool, n: Int }

                let zeroAtZ (rates: Map<String, Int>): Bool =
                    Map.get("Z", rates)
                        |> Option.map(r -> r == 0)
                        |> Option.withDefault(false)

                %s
                behavior priced : (deals: List<Deal>, rates: Rates) -> Tally
                    constructs Tally

                let priced (deals, rates) = {
                    guard rates.base == "reach" else Tally { ok = true, n = 0 }
                    let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                        |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                    guard List.length(weighed) == List.length(deals)
                        else Tally { ok = false, n = List.length(List.filter(
                            d -> d.currency == rates.base, deals)) }
                    Tally { ok = true, n = List.length(weighed) }
                }
                """.formatted(many);
    }

    @Test
    void theSearchSaysItStoppedAtTheFigureAndNoRunStopped() {
        Compilation compilation = compiled();
        ReachWitnesses.Sought sought = sought(compilation);

        assertEquals(Optional.empty(), sought.found());
        assertEquals(Set.of(STOPPED), sought.stoppedAt());
        assertEquals(Set.of(), sought.runsStopped());
    }

    @Test
    void whatTheRelationLeavesEachPlaceSaysTheFigureAWiderRunMayGetPast() {
        Compilation compilation = compiled();
        Map<String, PartitionEvidence.NotRead> byPlace = leftAtThePlaces(compilation);

        for (String place : PLACES) {
            PartitionEvidence.NotRead left = byPlace.get(place);
            assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                    left.reason(), byPlace.toString());
            assertEquals(List.of(STOPPED), left.figures(), left.toString());
            assertEquals(List.of(), left.runsStopped(), left.toString());
            BlockReason why = ((PartitionEvidence.NotRead.AnUnclassifiedRule) left).finding().why();
            assertEquals(RunSensitivity.MAY_CHANGE,
                    ((BlockReason.QuestionStandingReason) why).runSensitivity(), why.toString());
        }
    }

    @Test
    void thePageAndTheDocumentSayTheFigureForEachPlace() {
        Compilation compilation = compiled();
        String report = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
        for (String place : PLACES) {
            List<String> lines = report.lines().filter(line -> line.contains("not read: ")
                    && line.endsWith("`" + place + "`")).toList();
            assertEquals(1, lines.size(), report);
            assertTrue(lines.getFirst().contains(", stopped at how many values of an element are"
                    + " read for a count (VALUES_AN_ELEMENT_IS_CHOSEN_AMONG, 256), about `"),
                    lines.getFirst());
        }

        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        Map<String, JsonNode> figures = new LinkedHashMap<>();
        for (JsonNode each : notRead(document)) {
            if (each.path("reason").asString().equals("relation_not_shown_reached_at_every_value")) {
                figures.put(each.path("position").asString(), each.path("figures"));
            }
        }
        JsonNode said = JSON.readTree("[\"values_an_element_is_chosen_among\"]");
        assertEquals(Map.of(PLACES.get(0), said, PLACES.get(1), said), figures);
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSources(List.of(model()), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");
        return compilation;
    }

    /** What the reading leaves each place the relation compares, by the place. */
    private static Map<String, PartitionEvidence.NotRead> leftAtThePlaces(
            Compilation compilation) {
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        Map<String, PartitionEvidence.NotRead> byPlace = new LinkedHashMap<>();
        evidence.get("priced").notRead().forEach(each -> byPlace.put(each.at(), each));
        assertTrue(byPlace.keySet().containsAll(PLACES), byPlace.toString());
        return byPlace;
    }

    private static ReachWitnesses.Sought sought(Compilation compilation) {
        PartitionEvidence.NotRead left = leftAtThePlaces(compilation).get(PLACES.getFirst());
        SourceConstructOrigin relation = ((RuleRef.Comparison)
                ((PartitionEvidence.NotRead.AnUnclassifiedRule) left).rule()).origin();
        Set<ConditionOutcomeSite> reaching = new HashSet<>();
        compilation.db().ask(new Bodies.Observable("probe")).value().plan().sites()
                .forEach(site -> {
                    if (site instanceof CoverageSites.ComparisonSite compared
                            && compared.obligation().origin().equals(relation)) {
                        reaching.add(compared.index());
                    }
                });
        assertTrue(!reaching.isEmpty(), "a run going through the relation is recorded");
        return compilation.db().ask(new Adequacy.WitnessOfAReach("probe", "priced", reaching))
                .value();
    }

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
