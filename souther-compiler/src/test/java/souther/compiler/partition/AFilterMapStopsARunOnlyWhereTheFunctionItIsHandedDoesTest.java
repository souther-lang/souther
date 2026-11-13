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
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A {@code List.filterMap} stops a run only where the function it is handed does: what it does
 * apart from the function, a walk whose step matches on what the function answered and puts in
 * the value it holds, puts no more in than the list walked and stops nothing. A relation of the
 * code of each item and the keys of the prices, reached past it, is read at every value of both
 * ({@code rule_relating_two_values}), as past the {@code List.filter} keeping the same items. A
 * function taking a remainder by the length of the code stops a run only where the prices hold the
 * code, so a row holding the prices empty gets to the relation beside any code: the code is read
 * at every value, and the keys of the prices, which an empty table holds none of, are not shown
 * reached at every value. One taking a remainder by the price stops a run on the price alone,
 * which the relation does not read.
 */
class AFilterMapStopsARunOnlyWhereTheFunctionItIsHandedDoesTest {

    private static final String DECLARATIONS = """
            module probe

            data Item = { code: String, price: Int }
            data Prices = { known: Map<String, Int> }
            """;

    private static final String JUDGED = """

            behavior %1$s : (items: List<Item>, prices: Prices) -> Bool
            let %1$s (items, prices) = {
                let found = %2$s
                if List.length(found) == List.length(items) then true
                else List.all(i -> Map.containsKey(i.code, prices.known), items)
            }
            """;

    private static final List<String> RELATION = List.of("items[*].code", "prices.known[key]");
    private static final List<List<String>> READ = List.of(RELATION, List.of());
    private static final List<List<String>> ONLY_THE_KEYS_STOPPED =
            List.of(List.of("items[*].code"), List.of("prices.known[key]"));

    /** Each way of keeping the items, by name, and the places it leaves read as the relation of
     *  two values and those it leaves not shown reached at every value. */
    private static final Map<String, Case> CASES = cases();

    private record Case(String kept, List<List<String>> expected) {}

    private static Map<String, Case> cases() {
        Map<String, Case> out = new LinkedHashMap<>();
        out.put("viaFilter", new Case(
                "List.filter(i -> Map.containsKey(i.code, prices.known), items)", READ));
        out.put("viaFilterMap", new Case(
                "List.filterMap(i -> Map.get(i.code, prices.known), items)", READ));
        out.put("viaFilterMapDividingByTheCode", new Case("List.filterMap(i ->"
                + " Map.get(i.code, prices.known)"
                + " |> Option.map(p -> Int.floorMod(p, String.length(i.code))), items)",
                ONLY_THE_KEYS_STOPPED));
        out.put("viaFilterMapDividingByThePrice", new Case("List.filterMap(i ->"
                + " Map.get(i.code, prices.known)"
                + " |> Option.map(p -> Int.floorMod(p, i.price)), items)", READ));
        return out;
    }

    /** Every case measured, by name: one model, compiled and measured once for the class. */
    private static final Map<String, PartitionEvidence> MEASURED = measured();

    private static Map<String, PartitionEvidence> measured() {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        CASES.forEach((name, each) -> source.append(JUDGED.formatted(name, each.kept())));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(compilation);
        Map<String, PartitionEvidence> out =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        assertNotNull(out, "the model under test compiles");
        return out;
    }

    private static List<String> readAs(String name, UndividedPosition.Reason reason) {
        PartitionEvidence evidence = MEASURED.get(name);
        assertNotNull(evidence, () -> name + " is measured");
        return evidence.notRead().stream().filter(each -> each.reason() == reason)
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    @Test
    void aFilterMapIsReadPastAsAFilterIsAndOneWhoseFunctionMayStopOnTheCodeTiesIt() {
        Map<String, List<List<String>>> expected = new LinkedHashMap<>();
        Map<String, List<List<String>>> actual = new LinkedHashMap<>();
        CASES.forEach((name, each) -> {
            expected.put(name, each.expected());
            actual.put(name, List.of(
                    readAs(name, UndividedPosition.Reason.RULE_RELATING_TWO_VALUES),
                    readAs(name, UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)));
        });
        assertEquals(expected, actual);
    }
}
