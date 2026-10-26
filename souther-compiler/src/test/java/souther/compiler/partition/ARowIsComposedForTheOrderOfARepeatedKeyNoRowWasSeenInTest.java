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

    private static final String HEAD = """
            module p
            data LI = { sku: String, q: Int }
            data Empty = { n: Int }
            """;

    private static final String GUARD = """
                let stock = List.indexBy(%s, %s)
                guard List.all(i -> match Map.get(i.sku, stock) with
                    | Some r -> %s
                    | None -> i.q <= 0, items) else Empty { n = 0 }
                1
            """;

    private static List<String> keysIn(String rows, String field) {
        Matcher keys = Pattern.compile(field + " = (\"[^\"]*\")").matcher(rows);
        List<String> held = new ArrayList<>();
        while (keys.find()) {
            held.add(keys.group(1));
        }
        return held;
    }

    /**
     * What the container held is kept: a rule that asks for three elements is still met by the row
     * written for the order of a key, which is not rewritten into a list of two.
     */
    @Test
    void theElementsTheContainerHeldAreKept() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Row = { sku: String, qty: Int }
                behavior f : (items: List<LI>, rows: List<Row>) -> Int | Empty
                let f (items, rows) = {
                    guard List.length(rows) >= 3 else Empty { n = 2 }
                    let stock = List.indexBy(.sku, rows)
                    guard List.all(i -> match Map.get(i.sku, stock) with
                        | Some r -> r.qty >= i.q
                        | None -> i.q <= 0, items) else Empty { n = 1 }
                    1
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 9 },
                        Row { sku = "B", qty = 9 }, Row { sku = "C", qty = 9 }]) -> 1
                    | "short" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 1 },
                        Row { sku = "B", qty = 9 }, Row { sku = "C", qty = 9 }])
                        -> Empty { n = 1 }
                    | "few" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 9 }])
                        -> Empty { n = 2 }
                """);

        assertEquals(Set.of(CaseOfAStatement.Way.HOLDS_BY_THE_LAST,
                CaseOfAStatement.Way.FAILS_BY_THE_LAST), waysOf(found), found::toString);
        found.values().forEach(row -> assertTrue(
                keysIn(row.inputs().get(1).text(), "sku").size() >= 3,
                () -> "three elements at least: " + row.inputs().get(1).text()));
    }

    /**
     * A value a row does not hold is written: the order decides a statement over a {@code Bool}
     * only between a {@code true} and a {@code false}, and the rows written hold one of them.
     *
     * <p>Asked of the way that fails only. The way that holds needs a row composed at its rule
     * first, and the composer has no way to one here; that is not what this is about.
     */
    @Test
    void theOtherValueOfABoolIsWrittenForTheWayThatFails() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Row = { sku: String, ok: Bool }
                behavior f : (items: List<LI>, rows: List<Row>) -> Int | Empty
                let f (items, rows) = {
                    let stock = List.indexBy(.sku, rows)
                    guard List.all(i -> match Map.get(i.sku, stock) with
                        | Some r -> r.ok
                        | None -> false, items) else Empty { n = 0 }
                    1
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", ok = true }]) -> 1
                    | "absent" : ([LI { sku = "B", q = 5 }], [Row { sku = "A", ok = true }])
                        -> Empty { n = 0 }
                """);

        RowToRun row = found.entrySet().stream().filter(each -> each.getKey()
                        instanceof CaseOfAStatement.KeyOrder order
                        && order.way() == CaseOfAStatement.Way.FAILS_BY_THE_LAST)
                .findFirst().orElseThrow(() -> new AssertionError(found.toString())).getValue();
        String rows = row.inputs().get(1).text();
        assertTrue(rows.contains("ok = true") && rows.contains("ok = false"), rows);
    }

    /** A key below a record is held twice by the records, and what is given another value is the
     *  field below it that the statement reads. */
    @Test
    void aKeyBelowARecordIsHeldTwice() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Detail = { sku: String, qty: Int }
                data Row = { detail: Detail }
                behavior f : (items: List<LI>, rows: List<Row>) -> Int | Empty
                let f (items, rows) = {
                """ + GUARD.formatted("r -> r.detail.sku", "rows", "r.detail.qty >= i.q") + """
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }],
                        [Row { detail = Detail { sku = "A", qty = 9 } }]) -> 1
                    | "short" : ([LI { sku = "A", q = 5 }],
                        [Row { detail = Detail { sku = "A", qty = 1 } }]) -> Empty { n = 0 }
                """);

        assertEquals(Set.of(CaseOfAStatement.Way.HOLDS_BY_THE_LAST,
                CaseOfAStatement.Way.FAILS_BY_THE_LAST), waysOf(found), found::toString);
        found.values().forEach(row -> {
            List<String> held = keysIn(row.inputs().get(1).text(), "sku");
            assertEquals(2, held.size(), () -> row.inputs().get(1).text());
            assertEquals(held.get(0), held.get(1), () -> row.inputs().get(1).text());
        });
    }

    /** A field declared as a name over a number is given another number under the same name. */
    @Test
    void aFieldDeclaredAsANewtypeIsGivenAnotherValueUnderTheName() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Qty = Int
                data Row = { sku: String, qty: Qty }
                behavior f : (items: List<LI>, rows: List<Row>) -> Int | Empty
                let f (items, rows) = {
                """ + GUARD.formatted(".sku", "rows", "r.qty.value >= i.q") + """
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }],
                        [Row { sku = "A", qty = Qty(9) }]) -> 1
                    | "short" : ([LI { sku = "A", q = 5 }],
                        [Row { sku = "A", qty = Qty(1) }]) -> Empty { n = 0 }
                """);

        assertEquals(Set.of(CaseOfAStatement.Way.HOLDS_BY_THE_LAST,
                CaseOfAStatement.Way.FAILS_BY_THE_LAST), waysOf(found), found::toString);
        found.values().forEach(row -> assertTrue(
                row.inputs().get(1).text().split("Qty\\(", -1).length - 1 == 2,
                () -> row.inputs().get(1).text()));
    }

    /**
     * A field the rules keep the elements apart at differs between the two, so the container is one
     * the rules admit, and the row is not refused by the decoder it goes through.
     */
    @Test
    void aFieldTheRulesKeepApartDiffersBetweenTheTwo() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Row = { id: Int, sku: String, qty: Int }
                data Snap = { rows: List<Row> }
                    invariant List.allDistinctBy(.id, rows)
                behavior f : (items: List<LI>, snap: Snap) -> Int | Empty
                let f (items, snap) = {
                """ + GUARD.formatted(".sku", "snap.rows", "r.qty >= i.q") + """
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }],
                        Snap { rows = [Row { id = 1, sku = "A", qty = 9 }] }) -> 1
                    | "short" : ([LI { sku = "A", q = 5 }],
                        Snap { rows = [Row { id = 1, sku = "A", qty = 1 }] }) -> Empty { n = 0 }
                """);

        assertEquals(Set.of(CaseOfAStatement.Way.HOLDS_BY_THE_LAST,
                CaseOfAStatement.Way.FAILS_BY_THE_LAST), waysOf(found), found::toString);
        found.values().forEach(row -> {
            String snap = row.inputs().get(1).text();
            Matcher ids = Pattern.compile("id = (-?\\d+)").matcher(snap);
            List<String> held = new ArrayList<>();
            while (ids.find()) {
                held.add(ids.group(1));
            }
            assertEquals(2, held.size(), snap);
            assertTrue(!held.get(0).equals(held.get(1)), () -> "ids differ: " + snap);
            List<String> skus = keysIn(snap, "sku");
            assertEquals(skus.get(0), skus.get(1), snap);
        });
    }

    /** A field the rules keep apart that is a {@code Bool} is given its other value. */
    @Test
    void aBoolKeptApartIsGivenItsOtherValue() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Row = { slot: Bool, sku: String, qty: Int }
                data Snap = { rows: List<Row> }
                    invariant List.allDistinctBy(.slot, rows)
                behavior f : (items: List<LI>, snap: Snap) -> Int | Empty
                let f (items, snap) = {
                """ + GUARD.formatted(".sku", "snap.rows", "r.qty >= i.q") + """
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }],
                        Snap { rows = [Row { slot = true, sku = "A", qty = 9 }] }) -> 1
                    | "short" : ([LI { sku = "A", q = 5 }],
                        Snap { rows = [Row { slot = true, sku = "A", qty = 1 }] })
                        -> Empty { n = 0 }
                """);

        assertEquals(Set.of(CaseOfAStatement.Way.HOLDS_BY_THE_LAST,
                CaseOfAStatement.Way.FAILS_BY_THE_LAST), waysOf(found), found::toString);
        found.values().forEach(row -> {
            String snap = row.inputs().get(1).text();
            assertTrue(snap.contains("slot = true") && snap.contains("slot = false"), snap);
        });
    }

    /** A text the row holds one of is given another the composer writes at the type. */
    @Test
    void aTextTheRowHoldsOneOfIsGivenAnother() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Row = { sku: String, status: String }
                behavior f : (items: List<LI>, rows: List<Row>) -> Int | Empty
                let f (items, rows) = {
                """ + GUARD.formatted(".sku", "rows", "r.status == \"active\"") + """
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }],
                        [Row { sku = "A", status = "active" }]) -> 1
                    | "absent" : ([LI { sku = "B", q = 5 }],
                        [Row { sku = "A", status = "active" }]) -> Empty { n = 0 }
                """);

        assertTrue(!found.isEmpty(), "a row is written for some way");
        found.values().forEach(row -> {
            List<String> statuses = keysIn(row.inputs().get(1).text(), "status");
            assertEquals(2, statuses.size(), () -> row.inputs().get(1).text());
            assertTrue(!statuses.get(0).equals(statuses.get(1)), () -> row.inputs().get(1).text());
        });
    }

    /**
     * A case is offered only where a row can be written for it: a field whose type offers no other
     * value is no field to change, and so there is nothing to offer.
     */
    @Test
    void aCaseIsNotOfferedWhereTheFieldTheStatementReadsHasNoOtherValue() {
        Compilation compilation = Compilation.ofSource(HEAD + """
                data Card = { n: Int }
                data Cash = { n: Int }
                data Pay = Card | Cash
                data Row = { sku: String, pay: Pay }
                behavior f : (items: List<LI>, rows: List<Row>) -> Int | Empty
                let f (items, rows) = {
                    let stock = List.indexBy(.sku, rows)
                    guard List.all(i -> match Map.get(i.sku, stock) with
                        | Some r -> match r.pay with
                            | Card as c -> true
                            | Cash as c -> false
                        | None -> i.q <= 0, items) else Empty { n = 0 }
                    1
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }],
                        [Row { sku = "A", pay = Card { n = 1 } }]) -> 1
                    | "refused" : ([LI { sku = "A", q = 5 }],
                        [Row { sku = "A", pay = Cash { n = 1 } }]) -> Empty { n = 0 }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        String module = compilation.modules().getFirst();
        assertTrue(compilation.db().ask(new Adequacy.Decides(module)).value().get("f").took()
                        .made().orElseThrow().unseenCases().stream()
                        .anyMatch(each -> each instanceof CaseOfAStatement.KeyOrder),
                "the order is unmeasured, so that not being offered is the plan's answer");
        assertTrue(compilation.db().ask(new Adequacy.RowsOwed(module, "f")).value().cases()
                        .stream().noneMatch(each -> each instanceof CaseOfAStatement.KeyOrder),
                "no order is offered for a field with no other value to give");
    }

    /**
     * A list reached through the values of a map is a container the rewrite does not rebuild, so
     * the order of a key in it is reported unmeasured and no row is offered for it: what is
     * offered is what the rewrite does.
     */
    @Test
    void anOrderInAListBelowAMapIsNotOffered() {
        Compilation compilation = Compilation.ofSource(HEAD + """
                data Row = { sku: String, qty: Int }
                data Snap = { byDay: Map<String, List<Row>> }
                behavior f : (item: LI, snap: Snap) -> Int | Empty
                let f (item, snap) = {
                    guard match Map.get("d", snap.byDay) with
                        | Some rows -> match Map.get(item.sku, List.indexBy(.sku, rows)) with
                            | Some r -> r.qty >= item.q
                            | None -> false
                        | None -> false else Empty { n = 0 }
                    1
                }
                example f
                    | "stocked" : (LI { sku = "A", q = 5 },
                        Snap { byDay = [("d", [Row { sku = "A", qty = 9 }])] }) -> 1
                    | "short" : (LI { sku = "A", q = 5 },
                        Snap { byDay = [("d", [Row { sku = "A", qty = 1 }])] })
                        -> Empty { n = 0 }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        String module = compilation.modules().getFirst();
        assertTrue(compilation.db().ask(new Adequacy.Decides(module)).value().get("f").took()
                        .made().orElseThrow().unseenCases().stream()
                        .anyMatch(each -> each instanceof CaseOfAStatement.KeyOrder),
                "the order is unmeasured, so that not being offered is the plan's answer");
        assertTrue(compilation.db().ask(new Adequacy.RowsOwed(module, "f")).value().cases()
                        .stream().noneMatch(each -> each instanceof CaseOfAStatement.KeyOrder),
                "no order is offered for a list the rewrite does not go through");
    }

    /**
     * Nothing is made up for a field kept apart: a text the row holds only one of has no other
     * value to give the copy, and the row is not written with one invented for it.
     */
    @Test
    void aFieldKeptApartIsNotGivenAValueTheRowDoesNotOffer() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Row = { code: String, sku: String, qty: Int }
                data Snap = { rows: List<Row> }
                    invariant List.allDistinctBy(.code, rows)
                behavior f : (items: List<LI>, snap: Snap) -> Int | Empty
                let f (items, snap) = {
                """ + GUARD.formatted(".sku", "snap.rows", "r.qty >= i.q") + """
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }],
                        Snap { rows = [Row { code = "c", sku = "A", qty = 9 }] }) -> 1
                    | "short" : ([LI { sku = "A", q = 5 }],
                        Snap { rows = [Row { code = "c", sku = "A", qty = 1 }] })
                        -> Empty { n = 0 }
                """);

        assertTrue(found.isEmpty(), () -> "a code the row does not offer was made up: " + found);
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
