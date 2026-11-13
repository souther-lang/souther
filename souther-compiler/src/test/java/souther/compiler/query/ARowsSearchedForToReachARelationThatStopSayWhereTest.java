package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.DocumentShape;
import souther.compiler.check.RuleRef;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.SourceRendering;
import souther.compiler.execute.RunStop;
import souther.compiler.meta.ModulePath;
import souther.compiler.partition.ReachWitnesses;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.partition.WhereARunStopped;
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
 * Where a run may stop on the way to a relation and every row a search for one getting there tried
 * stops, the search says where the runs stopped, and so does what the relation leaves its place:
 * the report names the rule that refused the runs beside the word for the place, and the document
 * writes it under the entry for that place — as a search for a witness of a count says it.
 *
 * <p>The rates hold nought under one currency, so a deal in it stops a run at the remainder by its
 * rate before the relation, and the relation is not shown reached at every value. The relation is
 * on the way to the answer that is not ok, whose count is never more than how many deals there
 * are, and the {@code ensures} refuses every such answer — so every run the search for a row
 * getting to the relation tries stops there. Without the {@code ensures} the same search finds a
 * row and no run stops.
 */
class ARowsSearchedForToReachARelationThatStopSayWhereTest {

    private static final String ENSURES =
            "    ensures counted = value.ok || value.n > List.length(deals)";

    /** The two places the relation compares, each left not shown reached at every value. */
    private static final List<String> PLACES = List.of("deals[*].currency", "rates.base");

    private static String model(String ensures) {
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

                let zeroRates = Rates { rates = Map.fromList([ ("Z", 0) ]), base = "Z" }

                behavior priced : (deals: List<Deal>, rates: Rates) -> Tally
                    constructs Tally
                %s

                let priced (deals, rates) = {
                    let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                        |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                    guard List.length(weighed) == List.length(deals)
                        else Tally { ok = false, n = List.length(List.filter(
                            d -> d.currency == rates.base, deals)) }
                    Tally { ok = true, n = List.length(weighed) }
                }
                """.formatted(ensures);
    }

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** Where the runs stopped, as every entry of the document that says so writes it. */
    private static final String ENSURES_STOP = """
            [{"at": "an_ensures", "rule": "ensures priced (counted)", "module": "probe",
              "declaredIn": "probe"}]""";

    @Test
    void theSearchSaysWhereTheRunsOfTheRowsItTriedStopped() {
        Compilation compilation = compiled(model(ENSURES));
        ReachWitnesses.Sought sought = sought(compilation);

        assertEquals(Optional.empty(), sought.found());
        assertEquals(Set.of(theStop(compilation)), sought.runsStopped());
    }

    @Test
    void whatTheRelationLeavesEachPlaceSaysWhereTheRunsStopped() {
        Compilation compilation = compiled(model(ENSURES));
        Map<String, PartitionEvidence.NotRead> byPlace = leftAtThePlaces(compilation);

        for (String place : PLACES) {
            PartitionEvidence.NotRead left = byPlace.get(place);
            assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                    left.reason(), byPlace.toString());
            assertEquals(List.of(), left.shownReachedAt(), left.toString());
            assertEquals(List.of(theStop(compilation)), left.runsStopped(), left.toString());
        }
    }

    @Test
    void theReportNamesTheEnsuresBesideTheWordForEachPlace() {
        Compilation compilation = compiled(model(ENSURES));
        String report = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));

        for (String place : PLACES) {
            assertEquals(List.of("      · not read: comparison@24:29 — what it states was read,"
                            + " and it relates the value here to another value, but a run may stop"
                            + " on the way to it on values this compiler does not say, so not every"
                            + " value here is shown to get to it, and the runs stopped at the"
                            + " answer, where ensures priced (counted) did not hold, about `"
                            + place + "`"),
                    report.lines().filter(line -> line.contains("not read: ")
                            && line.endsWith("`" + place + "`")).toList(), report);
        }
    }

    @Test
    void theDocumentWritesWhereTheRunsStoppedUnderTheEntryForEachPlace() {
        Compilation compilation = compiled(model(ENSURES));
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);

        Map<String, JsonNode> stopped = new LinkedHashMap<>();
        for (JsonNode each : reachedAtEveryValue(document)) {
            stopped.put(each.path("position").asString(), each.path("runsStopped"));
        }
        JsonNode stop = JSON.readTree(ENSURES_STOP);
        assertEquals(Map.of(PLACES.get(0), stop, PLACES.get(1), stop), stopped);
    }

    /**
     * The control: without the ensures the same search finds a row, and no run stopped. The stop
     * turns on the currency, which stays not shown reached at every value; it turns on nothing the
     * base currency is, so a row holds any base beside it.
     */
    @Test
    void withoutTheEnsuresARowIsFoundAndNoRunStopped() {
        Compilation compilation = compiled(model(""));
        ReachWitnesses.Sought sought = sought(compilation);

        assertTrue(sought.found().isPresent(), sought.toString());
        assertEquals(Set.of(), sought.runsStopped());
        Map<String, PartitionEvidence.NotRead> byPlace = leftAtThePlaces(compilation);
        PartitionEvidence.NotRead currency = byPlace.get("deals[*].currency");
        assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                currency.reason(), byPlace.toString());
        assertEquals(List.of(), currency.runsStopped(), currency.toString());
        assertEquals(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES,
                byPlace.get("rates.base").reason(), byPlace.toString());
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        assertEquals(List.of(), reachedAtEveryValue(document).stream()
                .filter(each -> each.has("runsStopped")).toList());
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        return ACompiledModel.compiles(compilation);
    }

    /** Where every run on the way to the answer stops, as a run stopped there says it. */
    private static WhereARunStopped theStop(Compilation compilation) {
        return new WhereARunStopped(new RunStop.AtAnEnsures("probe", "priced",
                Optional.of("counted")), Optional.of(compilation.sourceIdOf("probe")));
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

    /** Every {@code notRead} entry saying a relation is not shown reached at every value. */
    private static List<JsonNode> reachedAtEveryValue(JsonNode document) {
        return notRead(document).stream().filter(each -> each.path("reason").asString()
                .equals("relation_not_shown_reached_at_every_value")).toList();
    }

    /** What the search for a row getting to the relation the places are left by came to, at a
     *  run going through the comparison it is written as. */
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
