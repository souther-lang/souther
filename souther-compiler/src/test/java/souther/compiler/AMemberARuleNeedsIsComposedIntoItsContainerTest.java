package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A container a rule needs to hold a member of the same value is composed holding it, and a value
 * it is to hold beside one it is to hold nothing equal to is composed as another value.
 *
 * <p>The table below rates its base, which its rule says; the deals are in currencies it does not
 * rate, which the point below the guard asks for two of. Composed against the guard alone, the
 * table was built empty and refused by its rule, and built holding the base it held the deals'
 * currency there too, since the base was the first value a currency is written as. So the point
 * was left open over a row the model has: two deals in one currency and a table rating another.
 *
 * <p>The rule is read where the declaration publishes it ({@code ClauseRead.Member}), the member
 * and the number the rule holds the value found under it to. A rate is composed as that number,
 * whichever value its type offers first, and a number its type refuses leaves the point open
 * rather than composing another value. The deals are cases of a sum whose fields every case
 * spreads, which is what crm's opportunities are: what is asked of a field under one case is
 * asked of the elements of that case, and an element of the other case holds nothing there.
 */
class AMemberARuleNeedsIsComposedIntoItsContainerTest {

    /** What every model below shares: the currencies, the deals and what the behavior answers. */
    private static final String DEALS = """
            data CurrencyCode = String
                invariant String.matches("[A-Z]{3}", value)

            data Common = { currency: CurrencyCode, amount: Decimal }
            data Early = { ...Common }
            data Late = { ...Common }
            data Deal = Early | Late

            data Priced = { n: Int }
            data Unpriced = { n: Int }
            data NoBase = { n: Int }
            """;

    /** The guard and the count below it, past whatever the first line asks, answering what the
     *  signature's answers are past {@code Priced | Unpriced}. */
    private static final String BODY = """
            behavior named : (deals: List<Deal>, rates: RateTable) -> Priced | Unpriced%s
                constructs Priced, Unpriced%s

            let named (deals, rates) = {
                %s
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(r -> r * d.amount), deals)
                guard List.length(weighed) == List.length(deals)
                    else Unpriced { n = List.length(List.filter(
                        d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals)) }
                Priced { n = List.length(weighed) }
            }
            """;

    /** The table's rule, a membership test. */
    private static final String RULED_BY_A_MEMBERSHIP = "module probe\n\n" + DEALS + """

            data RateTable = { base: CurrencyCode, rates: Map<CurrencyCode, Decimal> }
                invariant baseIsRated = Map.containsKey(base, rates)

            """ + BODY.formatted("", "", "");

    /** No rule on the table, and the body asking the same of it on the way. */
    private static final String ASKED_ON_THE_WAY = "module probe\n\n" + DEALS + """

            data RateTable = { base: CurrencyCode, rates: Map<CurrencyCode, Decimal> }

            """ + BODY.formatted(" | NoBase", ", NoBase",
            "guard Map.containsKey(rates.base, rates.rates) else NoBase { n = 0 }");

    @Test
    void aMemberATablesRuleNeedsByAMembershipTestIsComposedIntoIt() {
        assertEquals(List.of(), whatNothingCouldShow(RULED_BY_A_MEMBERSHIP));
    }

    @Test
    void aMemberTheWayAsksForBesideOneItIsToHoldNoneOfIsAnotherValue() {
        assertEquals(List.of(), whatNothingCouldShow(ASKED_ON_THE_WAY));
    }

    /** The table's rule through a helper, which asks the rate under the base to be a written
     *  number. {@code %s} are the type of a rate, and the number asked. */
    private static final String RULED_BY_A_HELPER = "module probe\n\n" + DEALS + """

            data ConversionRate = Decimal
                invariant value > 0.0m

            data RateTable = { base: CurrencyCode, rates: Map<CurrencyCode, %s> }
                invariant baseIsUnity = baseAtOne(base, rates)

            let baseAtOne (base: CurrencyCode, rates: Map<CurrencyCode, %s>): Bool =
                Map.get(base, rates)
                    |> Option.map(r -> Decimal.compare(r%s, %s) == 0)
                    |> Option.withDefault(false)

            """ + BODY.formatted("", "", "");

    /** The same rule written out as a match on the lookup. */
    private static final String RULED_BY_A_MATCH = "module probe\n\n" + DEALS + """

            data ConversionRate = Decimal
                invariant value > 0.0m

            data RateTable = { base: CurrencyCode, rates: Map<CurrencyCode, %s> }
                invariant baseIsUnity = match Map.get(base, rates) with
                    | Some r -> Decimal.compare(r%s, %s) == 0
                    | None -> false

            """ + BODY.formatted("", "", "");

    private static String byAHelper(String rate, String asked) {
        return RULED_BY_A_HELPER.formatted(rate, rate, valueOf(rate), asked);
    }

    private static String byAMatch(String rate, String asked) {
        return RULED_BY_A_MATCH.formatted(rate, valueOf(rate), asked);
    }

    /** What a rate is read as a number by: a name wrapping a decimal is read through its field. */
    private static String valueOf(String rate) {
        return rate.equals("Decimal") ? "" : ".value";
    }

    @Test
    void aRateASimpleTypeIsAskedToBeOneIsComposedHoldingIt() {
        assertEquals(List.of(), whatNothingCouldShow(byAHelper("Decimal", "1.0m")));
    }

    @Test
    void aRateASimpleTypeIsAskedToBeNoughtIsComposedHoldingIt() {
        assertEquals(List.of(), whatNothingCouldShow(byAHelper("Decimal", "0.0m")));
    }

    @Test
    void aRateAPositiveTypeIsAskedToBeOneIsComposedHoldingIt() {
        assertEquals(List.of(), whatNothingCouldShow(byAHelper("ConversionRate", "1.0m")));
    }

    @Test
    void aRateAPositiveTypeIsAskedToBeAnotherNumberIsComposedHoldingIt() {
        assertEquals(List.of(), whatNothingCouldShow(byAHelper("ConversionRate", "2.5m")));
    }

    @Test
    void aRateAskedForByAMatchIsComposedAsOneAskedForByAHelper() {
        assertEquals(List.of(), whatNothingCouldShow(byAMatch("ConversionRate", "2.5m")));
        assertEquals(List.of(), whatNothingCouldShow(byAMatch("Decimal", "1.0m")));
    }

    /** Helpers that ask the rate under a key to compare with a written number, and a table of
     *  rates under currencies whose keys are {@code %s}; the rules follow. */
    private static final String BY_KEYS = "module probe\n\n" + DEALS + """

            let at (key: CurrencyCode, rates: Map<CurrencyCode, Decimal>, n: Decimal): Bool =
                Map.get(key, rates)
                    |> Option.map(r -> Decimal.compare(r, n) == 0)
                    |> Option.withDefault(false)

            let above (key: CurrencyCode, rates: Map<CurrencyCode, Decimal>, n: Decimal): Bool =
                Map.get(key, rates)
                    |> Option.map(r -> Decimal.compare(r, n) > 0)
                    |> Option.withDefault(false)

            let below (key: CurrencyCode, rates: Map<CurrencyCode, Decimal>, n: Decimal): Bool =
                Map.get(key, rates)
                    |> Option.map(r -> Decimal.compare(r, n) < 0)
                    |> Option.withDefault(false)

            data RateTable = { %s, rates: Map<CurrencyCode, Decimal> }
            %s
            """ + BODY.formatted("", "", "");

    private static String byKeys(String keys, String... rules) {
        return BY_KEYS.formatted(keys, String.join("\n", rules));
    }

    @Test
    void twoEntriesOneRuleAsksOfOneMapAreComposedWhenTheirNumbersDiffer() {
        assertEquals(List.of(), whatNothingCouldShow(byKeys(
                "base: CurrencyCode, quote: CurrencyCode",
                "    invariant both = at(base, rates, 1.0m) && at(quote, rates, 2.0m)")));
    }

    @Test
    void twoEntriesTwoRulesAskOfOneMapAreComposedWhenTheirNumbersDiffer() {
        assertEquals(List.of(), whatNothingCouldShow(byKeys(
                "base: CurrencyCode, quote: CurrencyCode",
                "    invariant a = at(base, rates, 1.0m)",
                "    invariant b = at(quote, rates, 2.0m)")));
    }

    @Test
    void twoEntriesAskedTheSameNumberAreComposedAsOneOrTwo() {
        assertEquals(List.of(), whatNothingCouldShow(byKeys(
                "base: CurrencyCode, quote: CurrencyCode",
                "    invariant a = at(base, rates, 1.0m)",
                "    invariant b = at(quote, rates, 1.0m)")));
    }

    @Test
    void severalEntriesAskedDifferentNumbersAreEachComposedApartFromTheOthers() {
        assertEquals(List.of(), whatNothingCouldShow(byKeys(
                "a: CurrencyCode, b: CurrencyCode, c: CurrencyCode",
                "    invariant x = at(a, rates, 1.0m) && at(b, rates, 2.0m)",
                "    invariant y = at(c, rates, 3.0m)")));
    }

    @Test
    void aRateAskedToBeAboveANumberIsComposedAsANumberAboveIt() {
        assertEquals(List.of(), whatNothingCouldShow(byKeys("base: CurrencyCode",
                "    invariant a = above(base, rates, 5.0m)")));
    }

    @Test
    void aRateAskedToBeBelowANumberIsComposedAsANumberBelowIt() {
        assertEquals(List.of(), whatNothingCouldShow(byKeys("base: CurrencyCode",
                "    invariant a = below(base, rates, 5.0m)")));
    }

    @Test
    void aRateAskedForAboveOneNumberAndBelowAnotherIsComposedBetweenThem() {
        assertEquals(List.of(), whatNothingCouldShow(byKeys("base: CurrencyCode",
                "    invariant a = above(base, rates, 5.0m)",
                "    invariant b = below(base, rates, 6.0m)")));
    }

    @Test
    void ratesAskedForAboveAndBelowOneNumberOfOneKeyLeaveItsPointsOpen() {
        List<String> open = whatNothingCouldShow(byKeys("base: CurrencyCode",
                "    invariant a = above(base, rates, 6.0m)",
                "    invariant b = below(base, rates, 5.0m)"));
        assertTrue(open.stream().anyMatch(line -> line.contains("the ON point")), open::toString);
    }

    @Test
    void aRateNoValueOfItsTypeCanBeIsLeftOpenAndNotComposedAsAnother() {
        List<String> open = whatNothingCouldShow(byAHelper("ConversionRate", "0.0m"));
        assertFalse(open.isEmpty(), "no value a rate can be meets the rule, so the points are open");
        assertTrue(open.stream().anyMatch(line -> line.contains("the ON point")));
        assertTrue(open.stream().anyMatch(line -> line.contains("the OFF point")));
        assertTrue(open.stream().anyMatch(line -> line.contains("the OUT point")));
    }

    /** The points nothing could show a row can be written at. */
    private static List<String> whatNothingCouldShow(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        String page = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        List<String> found = new ArrayList<>();
        for (String line : page.split("\n")) {
            if (line.contains("nothing could show a row can be written at the ")) {
                found.add(line.trim());
            }
        }
        return found;
    }
}
