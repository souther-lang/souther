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

    /**
     * The way that holds is composed over a {@code Bool} as it is over a text: the rows written
     * for it hold the key twice, with the last of them {@code true}.
     */
    @Test
    void theValueOfABoolTheLastOneHoldsIsWrittenForTheWayThatHolds() {
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
                        && order.way() == CaseOfAStatement.Way.HOLDS_BY_THE_LAST)
                .findFirst().orElseThrow(() -> new AssertionError(found.toString())).getValue();
        String rows = row.inputs().get(1).text();
        List<String> keys = keysIn(rows, "sku");
        assertEquals(2, keys.size(), rows);
        assertEquals(keys.get(0), keys.get(1), rows);
        assertTrue(rows.indexOf("ok = false") >= 0 && rows.indexOf("ok = false")
                < rows.indexOf("ok = true"), rows);
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

    /**
     * The field the rules keep apart is the one the statement reads: the two copies already differ
     * there once they are given the values the order is told by, and a copy is not given a third
     * that makes them equal again.
     */
    @Test
    void aFieldKeptApartThatIsTheOneTheOrderIsToldByIsLeftAsItIsOnceItDiffers() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Row = { sku: String, ok: Bool }
                data Snap = { rows: List<Row> }
                    invariant List.allDistinctBy(.ok, rows)
                behavior f : (items: List<LI>, snap: Snap) -> Int | Empty
                let f (items, snap) = {
                """ + GUARD.formatted(".sku", "snap.rows", "r.ok") + """
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }],
                        Snap { rows = [Row { sku = "A", ok = true }] }) -> 1
                    | "refused" : ([LI { sku = "A", q = 5 }],
                        Snap { rows = [Row { sku = "A", ok = false }] }) -> Empty { n = 0 }
                """);

        assertTrue(!found.isEmpty(), "a row is written for the order");
        found.values().forEach(row -> {
            String snap = row.inputs().get(1).text();
            assertTrue(snap.contains("ok = true") && snap.contains("ok = false"), snap);
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
     * A field of a sum whose cases all carry something is given another value like any other:
     * one value of each case, written as the record the case is, so that the two copies of the
     * key hold different cases.
     */
    @Test
    void aSumWhoseCasesAllCarrySomethingIsGivenItsOtherCase() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
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
                """);

        assertEquals(Set.of(CaseOfAStatement.Way.HOLDS_BY_THE_LAST,
                CaseOfAStatement.Way.FAILS_BY_THE_LAST), waysOf(found),
                () -> "a row for each way: " + found.keySet());
        found.values().forEach(row -> {
            String rows = row.inputs().get(1).text();
            assertTrue(rows.contains("Card {") && rows.contains("Cash {"),
                    () -> "the two copies hold the two cases: " + rows);
        });
    }

    /**
     * The names a sum wears are put on once by the walk that rebuilds the row: the value written
     * for a case is the case, and a field of a sum declared under one name or under a name of
     * that name is written under each of them exactly once.
     */
    @Test
    void aSumDeclaredUnderANameIsWrittenUnderEachNameOnce() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Card = { n: Int }
                data Cash = { n: Int }
                data Pay = Card | Cash
                data PayN = Pay
                data PayNN = PayN
                data Row = { sku: String, pay: PayNN }
                behavior f : (items: List<LI>, rows: List<Row>) -> Int | Empty
                let f (items, rows) = {
                    let stock = List.indexBy(.sku, rows)
                    guard List.all(i -> match Map.get(i.sku, stock) with
                        | Some r -> match r.pay.value.value with
                            | Card as c -> true
                            | Cash as c -> false
                        | None -> i.q <= 0, items) else Empty { n = 0 }
                    1
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }],
                        [Row { sku = "A", pay = PayNN(PayN(Card { n = 1 })) }]) -> 1
                    | "refused" : ([LI { sku = "A", q = 5 }],
                        [Row { sku = "A", pay = PayNN(PayN(Cash { n = 1 })) }])
                        -> Empty { n = 0 }
                """);

        assertEquals(Set.of(CaseOfAStatement.Way.HOLDS_BY_THE_LAST,
                CaseOfAStatement.Way.FAILS_BY_THE_LAST), waysOf(found), found::toString);
        found.values().forEach(row -> {
            String rows = row.inputs().get(1).text();
            assertEquals(2, rows.split("PayNN\\(PayN\\(", -1).length - 1,
                    () -> "each copy under both names once: " + rows);
            assertTrue(!rows.contains("PayN(PayN(") && !rows.contains("PayNN(PayNN("),
                    () -> "no name twice: " + rows);
        });
    }

    /**
     * A case is not left out for coming after many: the statement tells the eighth case from the
     * rest, and the copies are given it.
     */
    @Test
    void aCaseAfterMoreThanAKindOfValuesHoldsIsStillWritten() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data C1 = { n: Int }
                data C2 = { n: Int }
                data C3 = { n: Int }
                data C4 = { n: Int }
                data C5 = { n: Int }
                data C6 = { n: Int }
                data C7 = { n: Int }
                data C8 = { n: Int }
                data Pay = C1 | C2 | C3 | C4 | C5 | C6 | C7 | C8
                data Row = { sku: String, pay: Pay }
                behavior f : (items: List<LI>, rows: List<Row>) -> Int | Empty
                let f (items, rows) = {
                    let stock = List.indexBy(.sku, rows)
                    guard List.all(i -> match Map.get(i.sku, stock) with
                        | Some r -> match r.pay with
                            | C1 as c -> true
                            | C2 as c -> true
                            | C3 as c -> true
                            | C4 as c -> true
                            | C5 as c -> true
                            | C6 as c -> true
                            | C7 as c -> true
                            | C8 as c -> false
                        | None -> i.q <= 0, items) else Empty { n = 0 }
                    1
                }
                example f
                    | "stocked" : ([LI { sku = "A", q = 5 }],
                        [Row { sku = "A", pay = C1 { n = 1 } }]) -> 1
                    | "refused" : ([LI { sku = "A", q = 5 }],
                        [Row { sku = "A", pay = C8 { n = 1 } }]) -> Empty { n = 0 }
                """);

        assertEquals(Set.of(CaseOfAStatement.Way.HOLDS_BY_THE_LAST,
                CaseOfAStatement.Way.FAILS_BY_THE_LAST), waysOf(found), found::toString);
        found.values().forEach(row -> assertTrue(row.inputs().get(1).text().contains("C8 {"),
                () -> "the eighth case is written: " + row.inputs().get(1).text()));
    }

    /**
     * The room is counted by case: a first case with more values than a listing holds does not
     * use it up, and the other case is still written.
     */
    @Test
    void aCaseWithManyValuesDoesNotCrowdOutTheNext() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Card = { a: Bool, b: Bool, c: Bool, d: Bool }
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
                        [Row { sku = "A", pay = Card { a = true, b = true, c = true, d = true } }])
                        -> 1
                    | "refused" : ([LI { sku = "A", q = 5 }],
                        [Row { sku = "A", pay = Cash { n = 1 } }]) -> Empty { n = 0 }
                """);

        assertTrue(!found.isEmpty(), "a row is written for some way");
        found.values().forEach(row -> {
            String rows = row.inputs().get(1).text();
            assertTrue(rows.contains("Card {") && rows.contains("Cash {"),
                    () -> "the two copies hold the two cases: " + rows);
        });
    }

    /**
     * A list reached through the values of a map is rebuilt around the map's own keys, so the
     * order of a key in it is composed for, with the entry's key and the other entries kept.
     */
    @Test
    void anOrderInAListBelowAMapIsComposedForWithTheKeysKept() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Row = { sku: String, qty: Int }
                data Snap = { byDay: Map<String, List<Row>> }
                behavior f : (item: LI, snap: Snap) -> Int | Empty
                let f (item, snap) = {
                    guard match Map.get(item.sku, snap.byDay) with
                        | Some rows -> match Map.get(item.sku, List.indexBy(.sku, rows)) with
                            | Some r -> r.qty >= item.q
                            | None -> false
                        | None -> false else Empty { n = 0 }
                    1
                }
                example f
                    | "stocked" : (LI { sku = "A", q = 5 },
                        Snap { byDay = [("A", [Row { sku = "A", qty = 9 }]),
                            ("e", [Row { sku = "Z", qty = 0 }])] }) -> 1
                    | "short" : (LI { sku = "A", q = 5 },
                        Snap { byDay = [("A", [Row { sku = "A", qty = 1 }]),
                            ("e", [Row { sku = "Z", qty = 0 }])] })
                        -> Empty { n = 0 }
                """);

        assertEquals(Set.of(CaseOfAStatement.Way.HOLDS_BY_THE_LAST,
                CaseOfAStatement.Way.FAILS_BY_THE_LAST), waysOf(found),
                () -> "a row for each way: " + found.keySet());
        found.values().forEach(row -> {
            String snap = row.inputs().get(1).text();
            List<String> keys = keysIn(snap, "sku");
            assertEquals(2, keys.size(), () -> "two elements: " + snap);
            assertEquals(keys.get(0), keys.get(1), () -> "holding one key: " + snap);
            assertTrue(snap.contains("byDay = [(" + keys.get(0) + ", ["),
                    () -> "the entry keeps its key: " + snap);
        });
    }

    /**
     * Where the map holds more than one entry, one entry's list is the one written again: the
     * others keep their keys and their elements.
     */
    @Test
    void theOtherEntriesOfTheMapAreKept() {
        Map<CaseOfAStatement, RowToRun> found = search(HEAD + """
                data Row = { sku: String, qty: Int }
                data Snap = { byDay: Map<String, List<Row>> }
                    invariant Map.size(byDay) >= 2
                behavior f : (item: LI, snap: Snap) -> Int | Empty
                let f (item, snap) = {
                    guard match Map.get(item.sku, snap.byDay) with
                        | Some rows -> match Map.get(item.sku, List.indexBy(.sku, rows)) with
                            | Some r -> r.qty >= item.q
                            | None -> false
                        | None -> false else Empty { n = 0 }
                    1
                }
                example f
                    | "stocked" : (LI { sku = "A", q = 5 },
                        Snap { byDay = [("A", [Row { sku = "A", qty = 9 }]),
                            ("e", [Row { sku = "Z", qty = 0 }])] }) -> 1
                    | "short" : (LI { sku = "A", q = 5 },
                        Snap { byDay = [("A", [Row { sku = "A", qty = 1 }]),
                            ("e", [Row { sku = "Z", qty = 0 }])] })
                        -> Empty { n = 0 }
                """);

        assertTrue(!found.isEmpty(), "a row is written for some way");
        found.values().forEach(row -> {
            String snap = row.inputs().get(1).text();
            Matcher entries = Pattern.compile("\\(\"[^\"]*\", \\[").matcher(snap);
            int keys = 0;
            while (entries.find()) {
                keys++;
            }
            assertEquals(2, keys, () -> "both entries kept: " + snap);
            assertEquals(3, keysIn(snap, "sku").size(),
                    () -> "one element added to one list, the other list as it was: " + snap);
        });
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
