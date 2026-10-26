package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Each way round the order of a key a map is filed by is a case a row can be composed for, and the
 * row that comes back holds the key twice and is one whose run was seen in the case.
 *
 * <p>The rows written hold each key once, so no row was seen in either way. What the composer
 * writes stands at the rule; the container is then written again with the key held twice, and the
 * run says whether the order decided the guard.
 */
class ARowIsComposedForTheOrderOfARepeatedKeyNoRowWasSeenInTest {

    private static final String MODEL = """
            module p
            data LI = { sku: String, q: Int }
            data Row = { sku: String, qty: Int }
            data Empty = { n: Int }
            behavior f : (items: List<LI>, rows: List<Row>) -> Int | Empty
            let f (items, rows) = {
                let stock = List.indexBy(.sku, rows)
                guard List.all(i -> match Map.get(i.sku, stock) with
                    | Some r -> r.qty >= i.q
                    | None -> i.q <= 0, items) else Empty { n = 0 }
                1
            }
            example f
                | "stocked" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 9 }]) -> 1
                | "short" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 1 }])
                    -> Empty { n = 0 }
            """;

    @Test
    void bothWaysRoundTheOrderAreComposed() {
        Map<CaseOfAStatement, RowToRun> found = search(MODEL);

        assertEquals(Set.of(CaseOfAStatement.Way.HOLDS_BY_THE_LAST,
                CaseOfAStatement.Way.FAILS_BY_THE_LAST), waysOf(found),
                () -> "a row for each way: " + found.keySet());
        found.forEach((each, row) -> {
            String rows = row.inputs().get(1).text();
            Matcher keys = Pattern.compile("sku = (\"[^\"]*\")").matcher(rows);
            List<String> held = new ArrayList<>();
            while (keys.find()) {
                held.add(keys.group(1));
            }
            assertEquals(2, held.size(), () -> "two elements: " + rows);
            assertEquals(held.get(0), held.get(1), () -> "holding one key: " + rows);
        });
    }

    /** The two copies of the element hold what a field the statement does not read held. */
    @Test
    void aFieldTheStatementDoesNotReadIsLeftAsItWas() {
        Map<CaseOfAStatement, RowToRun> found = search(MODEL
                .replace("data Row = { sku: String, qty: Int }",
                        "data Row = { sku: String, qty: Int, note: Int }")
                .replace("qty = 9 }", "qty = 9, note = 7 }")
                .replace("qty = 1 }", "qty = 1, note = 7 }"));

        assertEquals(Set.of(CaseOfAStatement.Way.HOLDS_BY_THE_LAST,
                CaseOfAStatement.Way.FAILS_BY_THE_LAST), waysOf(found), found::toString);
        found.values().forEach(row -> {
            Matcher notes = Pattern.compile("note = (-?\\d+)").matcher(row.inputs().get(1).text());
            List<String> held = new ArrayList<>();
            while (notes.find()) {
                held.add(notes.group(1));
            }
            assertEquals(2, held.size(), row.inputs().get(1)::text);
            assertEquals(held.get(0), held.get(1), () -> "an unread field is not moved: "
                    + row.inputs().get(1).text());
        });
    }

    private static Set<CaseOfAStatement.Way> waysOf(Map<CaseOfAStatement, RowToRun> found) {
        return found.keySet().stream()
                .filter(each -> each instanceof CaseOfAStatement.KeyOrder)
                .map(each -> ((CaseOfAStatement.KeyOrder) each).way())
                .collect(Collectors.toSet());
    }

    private static Map<CaseOfAStatement, RowToRun> search(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        DecisionEvidence evidence = compilation.db().ask(new Adequacy.Decides(module)).value()
                .get("f");
        List<CaseOfAStatement> unseen = evidence.took().made().orElseThrow().unseenCases();
        assertTrue(!unseen.isEmpty(), () -> "the rows leave an order unseen: " + evidence.took());
        return compilation.db().ask(new Adequacy.CaseSearch(module, "f")).value();
    }
}
