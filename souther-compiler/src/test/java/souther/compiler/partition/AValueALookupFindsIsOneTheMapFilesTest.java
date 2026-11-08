package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a lookup finds under a key is one of the values the map files, and what is worked out of
 * it stops a run on that value and on nothing else of the map: a rate found under a deal's
 * currency and multiplied by its amount ties the amount to the rates, and leaves a rule past it
 * about which currencies are keys of the rates reached as it is where the rate is answered as
 * found. Worked out of the currency as well, it ties the currency, and the rule is not shown
 * reached at every currency.
 */
class AValueALookupFindsIsOneTheMapFilesTest {

    private static final String DECLARATIONS = """
            module probe

            data Deal = { currency: String, amount: Decimal, p: Int }
            data Rates = { rates: Map<String, Decimal> }
            data Ok = { n: Int }
            data Missing = { n: Int }
            """;

    /** A weight for each deal its currency is priced in, and past a count of them, a rule about
     *  which currencies are priced. */
    private static final String JUDGED = """

            behavior %1$s : (deals: List<Deal>, rates: Rates) -> Ok | Missing
            let %1$s (deals, rates) = {
                let weighed = List.filterMap(d -> Map.get(d.currency, rates.rates)
                    |> Option.map(rate -> %2$s), deals)
                guard List.length(weighed) == List.length(deals)
                    else Missing { n = List.length(List.filter(
                        d -> Bool.not(Map.containsKey(d.currency, rates.rates)), deals)) }
                Ok { n = List.length(weighed) }
            }
            """;

    @Test
    void whatIsWorkedOutOfAValueFoundStopsARunOnThatValueAlone() {
        Map<String, String> judged = new LinkedHashMap<>();
        judged.put("asFound", "rate");
        judged.put("multiplied", "d.amount * rate");
        judged.put("rounded", "Decimal.round(2, HALF_UP, d.amount * rate * 0.01m)");
        judged.put("ofTheCurrency", "Decimal.fromInt(String.length(d.currency)) * rate");
        StringBuilder source = new StringBuilder(DECLARATIONS);
        judged.forEach((name, weight) -> source.append(JUDGED.formatted(name, weight)));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the models under test compile");
        Map<String, List<String>> priced = new LinkedHashMap<>();
        judged.keySet().forEach(name -> priced.put(name, evidence.get(name).notRead().stream()
                .filter(each -> each.at().equals("deals[*].currency")
                        || each.at().equals("rates.rates[key]"))
                .map(each -> each.at() + "=" + each.reason()).sorted().toList()));

        assertEquals(List.of(
                "deals[*].currency=" + UndividedPosition.Reason.RULE_RELATING_TWO_VALUES,
                "rates.rates[key]=" + UndividedPosition.Reason.RULE_RELATING_TWO_VALUES),
                priced.get("asFound"));
        for (String way : List.of("multiplied", "rounded")) {
            assertEquals(priced.get("asFound"), priced.get(way), way);
        }
        assertTrue(priced.get("ofTheCurrency").contains("deals[*].currency="
                        + UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE),
                priced.toString());
    }
}
