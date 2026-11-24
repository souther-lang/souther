package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a lookup finds under a key is one of the values the map files, and which one turns on the
 * key: a rule of the map may hold the value under one key to what stops a run, and a run with a
 * deal in that currency then never reaches a rule past the lookup. A rule past it about which
 * currencies are keys of the rates is reached at every currency only where nothing worked out of
 * what was found may stop the run.
 */
class AValueALookupFindsIsOneTheMapFilesTest {

    private static final String DECLARATIONS = """
            module probe

            data Deal = { currency: String, amount: Int }
            data Rates = { rates: Map<String, Int> }
                invariant zeroUnderZ = zeroAtZ(rates)
            data Ok = { n: Int }
            data Missing = { n: Int }

            let zeroAtZ (rates: Map<String, Int>): Bool =
                Map.get("Z", rates)
                    |> Option.map(r -> r == 0)
                    |> Option.withDefault(false)
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

    /**
     * A deal in the currency the rates hold at nought stops every run at the remainder by its
     * rate, so the rule is not reached at that currency, and is not said to be reached at every
     * one. A rate answered as found stops nothing, and the rule is reached at every currency.
     */
    @Test
    void aValueFoundUnderAKeyTheMapsRulesHoldIsNoValueChosenApartFromTheKey() {
        Map<String, String> judged = new LinkedHashMap<>();
        judged.put("asFound", "rate");
        judged.put("dividedBy", "Int.floorMod(d.amount, rate)");
        StringBuilder source = new StringBuilder(DECLARATIONS);
        judged.forEach((name, weight) -> source.append(JUDGED.formatted(name, weight)));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        Map<String, List<String>> priced = new LinkedHashMap<>();
        judged.keySet().forEach(name -> priced.put(name, evidence.get(name).notRead().stream()
                .filter(each -> each.at().equals("deals[*].currency"))
                .map(each -> each.at() + "=" + each.reason()).toList()));

        String reached = "deals[*].currency=" + UndividedPosition.Reason.RULE_RELATING_TWO_VALUES;
        assertEquals(List.of(reached), priced.get("asFound"), priced.toString());
        assertTrue(priced.get("dividedBy").stream().noneMatch(reached::equals),
                priced.toString());
        ACompiledModel.compiles(compilation);
    }
}
