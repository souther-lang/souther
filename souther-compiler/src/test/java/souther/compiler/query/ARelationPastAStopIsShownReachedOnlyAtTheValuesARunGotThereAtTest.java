package souther.compiler.query;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation a run may stop on the way to is not shown reached at every value, and a row built at
 * the boundary and run to it shows the values it holds there reached, and no other. The rates hold
 * nought under one currency, so a deal in that currency stops every run at the remainder by its
 * rate before the relation, and no row reaches the relation there: the values shown are the one
 * the row that got there held, which is not that currency, and the word stays what it was.
 */
class ARelationPastAStopIsShownReachedOnlyAtTheValuesARunGotThereAtTest {

    private static final String MODEL = """
            module probe

            data Deal = { currency: String, amount: Int }
            data Rates = { rates: Map<String, Int>, base: String }
                invariant zeroUnderZ = zeroAtZ(rates)
            data Ok = { n: Int }
            data Missing = { n: Int }

            let zeroAtZ (rates: Map<String, Int>): Bool =
                Map.get("Z", rates)
                    |> Option.map(r -> r == 0)
                    |> Option.withDefault(false)

            let zeroRates = Rates { rates = Map.fromList([ ("Z", 0) ]), base = "Z" }

            behavior priced : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let priced (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                        d -> d.currency == rates.base, deals)) }
                Ok { n = List.length(weighed) }
            }

            behavior unpriced : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let unpriced (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                        d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals)) }
                Ok { n = List.length(weighed) }
            }
            """;

    /** Two deals in two currencies, a walk stopping at the first it finds unpriced. */
    private static final String STOPPING_EARLY = """
            module probe

            data Deal = { currency: String, amount: Int }
            data Rates = { rates: Map<String, Int> }
            data Ok = { n: Int }
            data Missing = { n: Int }

            let twoDeals = [ Deal { currency = "X", amount = 1 }, Deal { currency = "Y", amount = 1 } ]
            let noRates = Rates { rates = Map.empty }

            behavior anyUnpriced : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let anyUnpriced (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = if List.any(
                        d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals)
                        then 1 else 0 }
                Ok { n = List.length(weighed) }
            }

            example anyUnpriced
                | "two deals no rate covers" : (twoDeals, noRates) -> Missing { n = 1 }
            """;

    @Test
    void aRowRunToTheRelationShowsTheValuesItHeldThereAndNoOther() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        Map<String, PartitionEvidence.NotRead> byPlace = new LinkedHashMap<>();
        evidence.get("priced").notRead().forEach(each -> byPlace.put(each.at(), each));

        PartitionEvidence.NotRead currency = byPlace.get("deals[*].currency");
        assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                currency.reason(), byPlace.toString());
        assertTrue(!currency.shownReachedAt().isEmpty(), byPlace.toString());
        assertTrue(!currency.shownReachedAt().contains("\"Z\""),
                "no run gets to the relation with a deal the rates hold at nought: " + byPlace);

        JsonNode document = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        List<String> written = new ArrayList<>();
        document.findValues("shownReachedAt").forEach(values ->
                values.forEach(each -> written.add(each.asString(""))));
        assertTrue(written.containsAll(currency.shownReachedAt()), written.toString());

        // An application of the library answering a truth is recorded where it answers, and a
        // row run through it shows the same.
        Map<String, PartitionEvidence.NotRead> ofTheLookup = new LinkedHashMap<>();
        evidence.get("unpriced").notRead().forEach(each -> ofTheLookup.put(each.at(), each));
        PartitionEvidence.NotRead looked = ofTheLookup.get("deals[*].currency");
        assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                looked.reason(), ofTheLookup.toString());
        assertTrue(!looked.shownReachedAt().isEmpty()
                        && !looked.shownReachedAt().contains("\"Z\""), ofTheLookup.toString());
    }

    /**
     * A row whose walk to the relation may stop at its first element shows the relation reached
     * at none of the values the row holds there: that a run went through it says at some, and not
     * at which.
     */
    @Test
    void aRowHoldingTwoValuesWhereAWalkStopsEarlyShowsNeither() {
        Compilation compilation = Compilation.ofSource(STOPPING_EARLY, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        List<String> shown = new ArrayList<>();
        evidence.get("anyUnpriced").notRead().forEach(each -> shown.addAll(each.shownReachedAt()));
        assertEquals(List.of(), shown, evidence.get("anyUnpriced").notRead().toString());
    }
}
