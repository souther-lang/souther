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

            let weightedOf (d: Deal, rates: Rates): Option<Int> =
                Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> Int.floorMod(d.amount, rate))

            let entry (d: Deal, rates: Rates): Option<Int> =
                weightedOf(d, rates) |> Option.map(w -> Int.floorMod(100, w + 1))

            let spreadThenEntry (d: Deal, rates: Rates): Option<Int> = {
                let spread = Int.floorMod(d.amount, String.length(d.currency))
                weightedOf(d, rates) |> Option.map(w -> w + spread)
            }

            let named (d: Deal, rates: Rates): Option<Int> = {
                let found = Map.get(d.currency, rates.rates)
                found |> Option.map(rate -> Int.floorMod(d.amount, rate))
            }

            behavior crossing : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let crossing (deals, rates) = {
                let weighed = List.filterMap(d -> entry(d, rates), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                        d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals)) }
                Ok { n = List.length(weighed) }
            }

            behavior spreadFirst : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let spreadFirst (deals, rates) = {
                let weighed = List.filterMap(d -> spreadThenEntry(d, rates), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                        d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals)) }
                Ok { n = List.length(weighed) }
            }

            behavior byName : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let byName (deals, rates) = {
                let weighed = List.filterMap(d -> named(d, rates), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                        d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals)) }
                Ok { n = List.length(weighed) }
            }

            behavior unpriced :(deals: List<Deal>, rates: Rates) -> Ok | Missing
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

    /**
     * A stop reading only how long a currency is, beside a relation of the currency and the keys of
     * a table. The divisor is nought at a length the default row does not hold, so a row gets to
     * the relation.
     */
    private static final String APART = """
            module probe

            data Deal = { currency: String, amount: Int }
            data Rates = { rates: Map<String, Int> }
            data Roomy = { rates: Map<String, Int> }
                invariant keyed = List.all(k -> String.length(k) > 0, Map.keys(rates))
            data Out = { n: Int }
            data Heavy = { xs: List<Int> }
                invariant two = List.length(xs) >= 2
                invariant big = List.all(x -> x >= 4611686018427387904, xs)
            data Pass = { active: Bool, currency: String, rates: Map<String, Int> }
                invariant zWhenPassive = active || Map.containsKey("Z", rates)
                invariant zeroZ = Map.get("Z", rates) |> Option.map(r -> r == 0)
                    |> Option.withDefault(true)

            behavior totalUnderTheKey : (deals: List<Deal>, rates: Rates, h: Heavy) -> Out
            let totalUnderTheKey (deals, rates, h) = {
                let total = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(r -> List.sum(h.xs)), deals)
                Out { n = List.length(List.filter(
                    d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals))
                    + List.length(total) }
            }

            behavior passive : (p: Pass) -> Out
            let passive (p) = {
                let spread = Map.get(p.currency, p.rates)
                    |> Option.map(r -> Int.floorMod(100, r)) |> Option.withDefault(0)
                if p.active then Out { n = 0 }
                else Out { n = if Map.containsKey(p.currency, p.rates) then spread else 1 }
            }

            behavior alone : (deals: List<Deal>, rates: Rates) -> Out
            let alone (deals, rates) = {
                let spread = List.map(d -> Int.floorMod(d.amount, String.length(d.currency) - 2),
                    deals)
                Out { n = List.length(List.filter(
                    d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals))
                    + List.length(spread) }
            }

            behavior onTheTable : (deals: List<Deal>, rates: Rates) -> Out
            let onTheTable (deals, rates) = {
                let spread = List.map(d -> Int.floorMod(d.amount,
                    String.length(d.currency) + Map.size(rates.rates) - 4), deals)
                Out { n = List.length(List.filter(
                    d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals))
                    + List.length(spread) }
            }

            behavior insideTheLookup : (deals: List<Deal>, rates: Rates) -> Out
            let insideTheLookup (deals, rates) = {
                let spread = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(r -> Int.floorMod(r, String.length(d.currency) - 2)), deals)
                let hit = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(r -> Bool.not(Map.containsKey(d.currency, rates.rates))), deals)
                Out { n = List.length(spread) + List.length(hit) }
            }

            let kept (ds: List<Deal>): List<Deal> = List.filter(d -> d.amount > 0, ds)

            behavior aloneOverWhatAFunctionKept : (deals: List<Deal>, rates: Rates) -> Out
            let aloneOverWhatAFunctionKept (deals, rates) = {
                let spread = List.map(d -> Int.floorMod(d.amount, String.length(d.currency) - 2),
                    kept(deals))
                Out { n = List.length(List.filter(
                    d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals))
                    + List.length(spread) }
            }

            behavior insideTheLookupOverWhatAFunctionKept :
                    (deals: List<Deal>, rates: Rates) -> Out
            let insideTheLookupOverWhatAFunctionKept (deals, rates) = {
                let spread = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(r -> Int.floorMod(r, String.length(d.currency) - 2)), kept(deals))
                let hit = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(r -> Bool.not(Map.containsKey(d.currency, rates.rates))),
                    kept(deals))
                Out { n = List.length(spread) + List.length(hit) }
            }

            behavior inTheLookup : (deals: List<Deal>, rates: Rates) -> Out
            let inTheLookup (deals, rates) = {
                let spread = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(r -> Int.floorMod(r, String.length(d.currency) - 2)), deals)
                Out { n = List.length(List.filter(
                    d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals))
                    + List.length(spread) }
            }

            behavior ruled : (deals: List<Deal>, rates: Roomy) -> Out
            let ruled (deals, rates) = {
                let spread = List.map(d -> Int.floorMod(d.amount, String.length(d.currency) - 2),
                    deals)
                Out { n = List.length(List.filter(
                    d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals))
                    + List.length(spread) }
            }

            behavior decided : (deals: List<Deal>, rates: Rates) -> Out
            let decided (deals, rates) = {
                let spread = List.map(d -> Int.floorMod(d.amount, String.length(d.currency) - 2),
                    deals)
                if Map.size(rates.rates) < 100
                then Out { n = List.length(List.filter(
                    d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals))
                    + List.length(spread) }
                else Out { n = 0 }
            }
            """;

    /** Why each place of {@code byPlace} is not read. */
    private static Map<String, UndividedPosition.Reason> reasonsOf(
            Map<String, PartitionEvidence.NotRead> byPlace) {
        Map<String, UndividedPosition.Reason> reasons = new LinkedHashMap<>();
        byPlace.forEach((place, each) -> reasons.put(place, each.reason()));
        return reasons;
    }

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

        // The same where the lookup is made in a function and its option is mapped in another.
        PartitionEvidence.NotRead across =
                currencyOf(evidence, "crossing").get("deals[*].currency");
        assertTrue(across == null || across.reason()
                != UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                currencyOf(evidence, "crossing").toString());

        // And where the lookup is held in a name the body gave it.
        PartitionEvidence.NotRead named = currencyOf(evidence, "byName").get("deals[*].currency");
        assertTrue(named == null || named.reason()
                != UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                currencyOf(evidence, "byName").toString());

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
        for (String behavior : List.of("spreading", "tabled", "uncounted", "amountless",
                "spreadFirst")) {
            PartitionEvidence.NotRead stopped =
                    currencyOf(evidence, behavior).get("deals[*].currency");
            assertNotEquals(null, stopped, behavior + " " + currencyOf(evidence, behavior));
            assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                    stopped.reason(), behavior + " " + currencyOf(evidence, behavior));
        }
    }

    /**
     * A place nothing the run stops on, narrows by or decides by reads, which no rule names, is
     * the same run at every value a row holds there. A stop reading the currency leaves the
     * currency stopped and the keys of the table not.
     */
    @Test
    void aStopThatReadsOtherPlacesLeavesThisOneReachedAtEveryValue() {
        Compilation compilation = Compilation.ofSource(APART, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), compilation.errors().toString());

        assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                currencyOf(evidence, "alone").get("deals[*].currency").reason(),
                currencyOf(evidence, "alone").toString());
        assertNotEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                currencyOf(evidence, "alone").get("rates.rates[key]").reason(),
                currencyOf(evidence, "alone").toString());

        // The relation is itself reached only where the table holds the currency, so a row holding
        // the table empty gets to nothing and the stop it avoids is no stop avoided.
        assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                currencyOf(evidence, "insideTheLookup").get("deals[*].currency").reason(),
                currencyOf(evidence, "insideTheLookup").toString());

        // A container a function made is read as the function's body makes it, so the same
        // shapes over it come out as they do over the library's own.
        for (String twin : List.of("alone", "insideTheLookup")) {
            assertEquals(reasonsOf(currencyOf(evidence, twin)), reasonsOf(currencyOf(evidence,
                    twin + "OverWhatAFunctionKept")), twin);
        }

        // A total that cannot fit is worked out only where the lookup finds the currency. A row
        // holding the table empty never works it out, so the currency is reached at every value;
        // the keys of the table are what the lookup is made in, and stay not shown.
        assertNotEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                currencyOf(evidence, "totalUnderTheKey").get("deals[*].currency").reason(),
                currencyOf(evidence, "totalUnderTheKey").toString());
        assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                currencyOf(evidence, "totalUnderTheKey").get("rates.rates[key]").reason(),
                currencyOf(evidence, "totalUnderTheKey").toString());

        // A rule ties the way to the table: the way holds only where the table has a currency
        // whose rate stops the run, so no row holding the table empty is a row of the way.
        assertNotEquals(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES,
                currencyOf(evidence, "passive").get("p.currency").reason(),
                currencyOf(evidence, "passive").toString());

        // The stop reads the table as well, is worked out only where the table holds the currency
        // (which turns on its keys), a rule names the table, or the way decides by it.
        for (String behavior : List.of("onTheTable", "inTheLookup", "ruled", "decided")) {
            assertEquals(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE,
                    currencyOf(evidence, behavior).get("rates.rates[key]").reason(),
                    behavior + " " + currencyOf(evidence, behavior));
        }
    }
}
