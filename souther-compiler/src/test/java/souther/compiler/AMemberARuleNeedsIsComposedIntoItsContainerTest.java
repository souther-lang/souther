package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

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
 * <p>The rule is read where the declaration publishes it ({@code ClauseRead.Member}), and what is
 * composed is the member and not anything a rule asks of it: a lookup whose rule holds the value
 * found to something asks that of a value this writes as its type's rules leave it. The deals
 * are cases of a sum whose fields every case spreads, which is what crm's opportunities are: what
 * is asked of a field under one case is asked of the elements of that case, and an element of the
 * other case holds nothing there.
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
