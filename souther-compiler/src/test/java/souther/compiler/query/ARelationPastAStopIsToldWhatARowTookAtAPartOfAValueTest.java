package souther.compiler.query;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.report.AdequacyReport;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation a run may stop on the way to is told what a row run to it took at a place that is a
 * part of a date, or a key a map is looked up by, as it is told what the row held at a place that
 * is a value. The rates hold nought under one currency, so a deal in it stops every run at the
 * remainder by its rate, and the relation is not shown reached at every value of what it reads.
 */
class ARelationPastAStopIsToldWhatARowTookAtAPartOfAValueTest {

    private static final String RATES = """
            module probe

            data Deal = { currency: String, amount: Int, on: Date }
            data Rates = { rates: Map<String, Int>, year: Int }
                invariant zeroUnderZ = zeroAtZ(rates)
            data Ok = { n: Int }
            data Missing = { n: Int }

            let zeroAtZ (rates: Map<String, Int>): Bool =
                Map.get("Z", rates)
                    |> Option.map(r -> r == 0)
                    |> Option.withDefault(false)
            """;

    private static final String SEEDED = RATES + """

            let zeroRates = Rates { rates = Map.fromList([ ("Z", 0) ]), year = 2000 }
            let oneDeal: List<Deal> = [ Deal { currency = "Q", amount = 1,
                                               on = Date("2026-07-01") } ]

            behavior dated : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let dated (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                        d -> Date.year(d.on) == rates.year, deals)) }
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

            behavior moved : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let moved (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                            d -> Date.month(Date.addDays(0 - 1, d.on)) == rates.year, deals))
                        + List.length(List.filter(d -> Date.day(d.on) == rates.year, deals)) }
                Ok { n = List.length(weighed) }
            }

            behavior summed : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let summed (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = if List.sum(List.map(d -> d.amount, deals)) == rates.year
                        then 1 else 0 }
                Ok { n = List.length(weighed) }
            }
            """;

    /**
     * Groups of which the first has no key looked for, the second is ready and the third holds
     * it. The groups are walked until one is ready, and the table of each is searched for the key
     * looked for only while they are, so the table of the third is not searched at all: a key it
     * holds is not one the search was made at, though it equals the key looked for.
     */
    private static final String GROUPS = RATES + """

            data Group = { ready: Bool, table: Map<String, Int> }

            let groups: List<Group> = [
                Group { ready = false, table = Map.fromList([ ("A", 1) ]) },
                Group { ready = true, table = Map.empty },
                Group { ready = false, table = Map.fromList([ ("B", 1) ]) } ]
            let wantedB: String = "B"
            let zeroRates = Rates { rates = Map.fromList([ ("Z", 0) ]), year = 2000 }

            behavior anyGroup : (groups: List<Group>, wanted: String, rates: Rates) -> Ok
            let anyGroup (groups, wanted, rates) = {
                let share = Map.get(wanted, rates.rates)
                    |> Option.map(rate -> Int.floorMod(7, rate))
                    |> Option.withDefault(0)
                Ok { n = share + (if List.any(
                    g -> g.ready || Map.containsKey(wanted, g.table), groups) then 1 else 0) }
            }
            """;

    /**
     * Two deals, one in each of two currencies, and a currency looked for. A scan that goes on
     * while every deal is in the currency looked for ends at the first deal that is not, so the
     * deal in the currency looked for, which comes after it, is not one the comparison was made
     * on: the currency is not told at it, though it equals the currency looked for.
     */
    private static final String A_SCAN = RATES + """

            let day = Date("2026-07-01")
            let twoDeals: List<Deal> = [ Deal { currency = "A", amount = 1, on = day },
                                         Deal { currency = "B", amount = 1, on = day } ]
            let wantedB: String = "B"
            let zeroRates = Rates { rates = Map.fromList([ ("Z", 0) ]), year = 2000 }

            behavior everyDealIn : (deals: List<Deal>, wanted: String, rates: Rates) -> Ok
            let everyDealIn (deals, wanted, rates) = {
                let share = Map.get(wanted, rates.rates)
                    |> Option.map(rate -> Int.floorMod(7, rate))
                    |> Option.withDefault(0)
                Ok { n = share + (if List.all(d -> d.currency == wanted, deals) then 1 else 0) }
            }
            """;

    /**
     * Two deals, in two currencies, and rates holding two currencies, one of them a deal's. The
     * count of the deals the rates cover is made at each deal's currency, so of the two keys the
     * rates hold only the one a deal is in is a key the relation was read at. A deal in the
     * currency held at nought stops a run before the count, so the relation is not shown reached
     * at every value.
     */
    private static final String TWO_KEYS = RATES + """

            let day = Date("2026-07-01")
            let mixedDeals: List<Deal> = [ Deal { currency = "Y", amount = 1, on = day },
                                           Deal { currency = "W", amount = 1, on = day } ]
            let twoRates = Rates { rates = Map.fromList([ ("Z", 0), ("Y", 1) ]), year = 2000 }

            behavior covered : (deals: List<Deal>, rates: Rates) -> Ok
            let covered (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                Ok { n = List.length(weighed) + List.length(List.filter(
                    d -> Map.containsKey(d.currency, rates.rates), deals)) }
            }
            """;

    /**
     * No value of the model names rates, so no row is found that gets to the relation, and the
     * relation compared with a count of the deals is a relation among counts of one container
     * with nothing beside it that the container is composed for.
     */
    private static final String UNSEEDED = RATES + """

            behavior priced : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let priced (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                        d -> d.currency == "Z" && Date.year(d.on) > rates.year, deals)) }
                Ok { n = List.length(weighed) }
            }
            """;

    @Test
    void aPartOfADateAndAKeyAreToldWhatTheRowRunToTheRelationTookThere() {
        Compilation compilation = onTheDay(SEEDED);
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();

        PartitionEvidence.NotRead year = notRead(evidence, "dated").get("Date.year(deals[*].on)");
        assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                year.reason(), year.toString());
        assertEquals(List.of("2026"), year.shownReachedAt(), year.toString());

        Map<String, PartitionEvidence.NotRead> unpriced = notRead(evidence, "unpriced");
        PartitionEvidence.NotRead key = unpriced.get("rates.rates[key]");
        assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                key.reason(), unpriced.toString());
        assertEquals(List.of("\"Z\""), key.shownReachedAt(), key.toString());
        assertEquals(List.of("\"Q\""), unpriced.get("deals[*].currency").shownReachedAt(),
                "a place that is a value is told as it was");

        JsonNode document = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        List<String> written = new ArrayList<>();
        document.findValues("shownReachedAt").forEach(values ->
                values.forEach(each -> written.add(each.asString(""))));
        assertTrue(written.containsAll(List.of("2026", "\"Z\"")), written.toString());
        ACompiledModel.compiles(compilation);
    }

    @Test
    void aKeyIsToldOnlyAtTheKeysTheLookupWasMadeAt() {
        Compilation compilation = onTheDay(TWO_KEYS);
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();

        Map<String, PartitionEvidence.NotRead> covered = notRead(evidence, "covered");
        assertEquals(List.of("\"Y\"", "\"W\""), covered.get("deals[*].currency").shownReachedAt(),
                covered.toString());
        assertEquals(List.of("\"Y\""), covered.get("rates.rates[key]").shownReachedAt(),
                covered.toString());
        ACompiledModel.compiles(compilation);
    }

    /**
     * A part of a date a move put elsewhere is told as the moved date has it and not as the date
     * stands, and a total is told as the row's elements come to.
     */
    @Test
    void aMovedDatesPartAndATotalAreToldAsTheRowTookThem() {
        Map<String, PartitionEvidence> evidence = evidenceOf(SEEDED);

        Map<String, PartitionEvidence.NotRead> moved = notRead(evidence, "moved");
        assertEquals(List.of("6"), toldAt(moved, "Date.month"), moved.toString());
        assertEquals(List.of("1"), toldAt(moved, "Date.day"), moved.toString());
        Map<String, PartitionEvidence.NotRead> summed = notRead(evidence, "summed");
        assertEquals(List.of("1"), toldAt(summed, "List.sum"), summed.toString());
    }

    @Test
    void aScanThatEndsAtTheFirstUnequalElementIsNotToldTheEqualOnesAfterIt() {
        Map<String, PartitionEvidence.NotRead> scanned =
                notRead(evidenceOf(A_SCAN), "everyDealIn");

        assertEquals(List.of("\"B\""), toldAt(scanned, "wanted"),
                "the row got there, which the currency looked for says: " + scanned);
        assertEquals(List.of(), toldAt(scanned, "deals[*].currency"), scanned.toString());
    }

    /**
     * A search inside an element of another container is one for each of them, and a run that went
     * through it went through the search of some, so the keys the row holds in the tables of the
     * others are not told as keys the search was made at.
     */
    @Test
    void aSearchInsideAnElementIsNotToldTheKeysOfTheElementsItWasNotMadeIn() {
        Map<String, PartitionEvidence.NotRead> scanned =
                notRead(evidenceOf(GROUPS), "anyGroup");

        assertEquals(List.of("\"B\""), toldAt(scanned, "wanted"),
                "the row got there, which the key looked for says: " + scanned);
        assertTrue(!toldAt(scanned, "table[key]").contains("\"B\""), scanned.toString());
    }

    private static Map<String, PartitionEvidence> evidenceOf(String source) {
        Compilation compilation = onTheDay(source);
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        ACompiledModel.compiles(compilation);
        return evidence;
    }

    /** What is told at the one place of {@code byPlace} that is written with {@code part}. */
    private static List<String> toldAt(Map<String, PartitionEvidence.NotRead> byPlace,
                                       String part) {
        List<PartitionEvidence.NotRead> at = byPlace.entrySet().stream()
                .filter(each -> each.getKey().contains(part)).map(Map.Entry::getValue).toList();
        assertEquals(1, at.size(), part + " in " + byPlace);
        return at.getFirst().shownReachedAt();
    }

    /**
     * A relation among counts of one container that nothing else asks counts beside is measured
     * as any other is, and no row got to it, so no value is told for the places it leaves.
     */
    @Test
    void aRelationAmongCountsAskedAloneIsMeasuredAndNoValueIsToldForIt() {
        Compilation compilation = onTheDay(UNSEEDED);
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();

        Map<String, PartitionEvidence.NotRead> byPlace = notRead(evidence, "priced");
        assertTrue(!byPlace.isEmpty(), byPlace.toString());
        byPlace.forEach((at, each) -> assertEquals(List.of(), each.shownReachedAt(), at));
        ACompiledModel.compiles(compilation);
    }

    /** A compilation writing rows on a day the test fixes, so that what a search generates where the model
     *  names nothing does not turn on the day the test runs. */
    private static Compilation onTheDay(String source) {
        return Compilation.ofSource(source, "Main").writtenOn(LocalDate.of(2026, 11, 9));
    }

    private static Map<String, PartitionEvidence.NotRead> notRead(
            Map<String, PartitionEvidence> evidence, String behavior) {
        Map<String, PartitionEvidence.NotRead> byPlace = new LinkedHashMap<>();
        evidence.get(behavior).notRead().forEach(each -> byPlace.put(each.at(), each));
        return byPlace;
    }
}
