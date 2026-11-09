package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.UndividedPosition;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An operator inside the closure of {@code Option.map} over {@code Map.get(currency, rates)} stops
 * a run only where the table holds the currency. A row holding the table empty beside any currency
 * works out none of it, and gets to the relation, so the stop does not turn on the currency and
 * the place is not left for it. Where the table may not be empty, or an operator reads the
 * currency outside the lookup, some value of the currency is stopped and the place stays left.
 */
class ARelationPastAStopTheValueDoesNotTurnOnIsReachedAtEveryValueTest {

    private static final String MODEL = """
            module probe

            data Deal = { currency: String, amount: Int }
            data Rates = { rates: Map<String, Int> }
            data Table = { rates: Map<String, Int> }
                invariant oneAtLeast = Map.size(rates) >= 1
            data Ok = { n: Int }
            data Missing = { n: Int }
            data Book = { currency: String, rates: Map<String, Int> }
                invariant emptyOnlyForX = Map.size(rates) >= 1 || currency == "x"

            behavior correlated : (book: Book) -> Ok | Missing
            let correlated (book) = {
                let w = Map.get(book.currency, book.rates)
                    |> Option.map(rate -> Int.floorMod(1, rate)) |> Option.withDefault(0)
                if Map.containsKey(book.currency, book.rates) then Ok { n = w } else Missing { n = w }
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

            behavior spreading : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let spreading (deals, rates) = {
                let spread = List.map(d -> Int.floorMod(d.amount, String.length(d.currency)), deals)
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                        d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals)) }
                Ok { n = List.length(weighed) + List.length(spread) }
            }

            behavior tabled : (deals: List<Deal>, rates: Table) -> Ok | Missing
            let tabled (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                        d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals)) }
                Ok { n = List.length(weighed) }
            }

            behavior uncounted : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let uncounted (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                guard List.length(List.filter(d -> d.amount > 0, deals)) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                        d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals)) }
                Ok { n = List.length(weighed) }
            }

            behavior amountless :(deals: List<Deal>, rates: Rates) -> Ok | Missing
            let amountless (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate)), deals)
                guard List.length(weighed) == List.length(deals) && List.length(deals) > 1
                    else Missing { n = List.length(List.filter(
                        d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals)) }
                Ok { n = List.length(weighed) }
            }
            """;

    private static Map<String, PartitionEvidence.NotRead> currencyOf(
            Map<String, PartitionEvidence> evidence, String behavior) {
        Map<String, PartitionEvidence.NotRead> byPlace = new LinkedHashMap<>();
        evidence.get(behavior).notRead().forEach(each -> byPlace.put(each.at(), each));
        return byPlace;
    }

    @Test
    void aStopThatTurnsOnNoValueOfAPlaceLeavesNoValueOfItNotShownReached() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(),
                compilation.errors().toString());

        // The table may be held empty, so no run is stopped at any currency.
        PartitionEvidence.NotRead free = currencyOf(evidence, "unpriced").get("deals[*].currency");
        assertTrue(free == null || free.reason()
                != UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                currencyOf(evidence, "unpriced").toString());

        // The table is not shown to be reached at every key of it: a key is a value of the
        // table, and an empty table holds none.
        assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                currencyOf(evidence, "unpriced").get("rates.rates[key]").reason(),
                currencyOf(evidence, "unpriced").toString());

        // A rule letting the table be empty only beside one currency leaves the others stopped.
        PartitionEvidence.NotRead correlated =
                currencyOf(evidence, "correlated").get("book.currency");
        assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                correlated == null ? null : correlated.reason(),
                currencyOf(evidence, "correlated").toString());

        // An operator reading the currency outside the lookup stops a run at some currency.
        for (String behavior : List.of("spreading", "tabled", "uncounted", "amountless")) {
            PartitionEvidence.NotRead stopped =
                    currencyOf(evidence, behavior).get("deals[*].currency");
            assertNotEquals(null, stopped, behavior + " " + currencyOf(evidence, behavior));
            assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                    stopped.reason(), behavior + " " + currencyOf(evidence, behavior));
        }
    }
}
