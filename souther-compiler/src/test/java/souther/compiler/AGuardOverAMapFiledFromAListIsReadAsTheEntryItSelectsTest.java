package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A lookup in a map filed from a list answers the last element of the key asked for, and a guard
 * over it is read of that element and not of another.
 *
 * <p>Said as the statement it is: some element of the rows holds the key, no later element holds
 * it, and of that one the quantity meets what the arm asks. A row offered for a line of the quantity
 * is one whose last element of the key is the one at the line.
 */
class AGuardOverAMapFiledFromAListIsReadAsTheEntryItSelectsTest {

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
            """;

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> errors(Compilation compilation) {
        return compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList();
    }

    /** The oracle: a quantity per key as the lookup answers it, the last row of a key winning. */
    private static boolean admits(List<String[]> items, List<String[]> rows) {
        Map<String, Long> stock = new LinkedHashMap<>();
        for (String[] row : rows) {
            stock.put(row[0], Long.parseLong(row[1]));
        }
        for (String[] item : items) {
            long wanted = Long.parseLong(item[1]);
            boolean holds = stock.containsKey(item[0]) ? stock.get(item[0]) >= wanted
                    : wanted <= 0;
            if (!holds) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether everything {@code report} says went unread is that a relation is not shown to reach
     * every value of a place.
     *
     * <p>Which row of the rows the lookup answers is the one whose key is asked, so the quantity it
     * holds is the quantity of a row a condition on the keys picked out, and what it reaches beside
     * the item's quantity is not shown. The comparison itself was read.
     */
    private static boolean readSaveForWhatTheOtherValueReaches(String report) {
        return report.lines().filter(line -> line.strip().startsWith("· not read"))
                .allMatch(line -> line.contains("not shown to reach every value here"));
    }

    @Test
    void theGuardIsReadToTheEnd() {
        String report = report(measured(MODEL));

        assertTrue(readSaveForWhatTheOtherValueReaches(report), report);
        assertTrue(report.contains("borders 2"), report);
    }

    /**
     * The last value for a repeated key is read as the last one, and which decisions turn on the
     * order was not measured: the rows written hold each key once. So the measurement says it is
     * partial, in the word for that — and beside it only what the relation is not shown to reach.
     */
    @Test
    void theOrderOfARepeatedKeyIsSaidToBeUnmeasured() throws Exception {
        Compilation compilation = measured(MODEL);
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
        JsonNode document = JSON.readTree(json);

        assertTrue(report(compilation).contains("measurement: partial"),
                () -> report(compilation));
        List<String> words = new ArrayList<>();
        collectWeakening(document, words);
        assertTrue(words.contains("keyed_overwrite_cases_unmeasured"), words::toString);
        assertTrue(readSaveForWhatTheOtherValueReaches(report(compilation)),
                () -> report(compilation));
    }

    /** What is said of a model whose map is built a key at a time is not said of this one. */
    @Test
    void aLookupInAMapNobodyFiledFromAListSaysNothingOfTheOrder() throws Exception {
        Compilation compilation = measured("""
                module p
                data LI = { sku: String, q: Int }
                data Empty = { n: Int }
                behavior f : (items: List<LI>, stock: Map<String, Int>) -> Int | Empty
                let f (items, stock) = {
                    guard List.all(i -> match Map.get(i.sku, stock) with
                        | Some r -> r >= i.q
                        | None -> i.q <= 0, items) else Empty { n = 0 }
                    1
                }
                """);
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
        List<String> words = new ArrayList<>();
        collectWeakening(JSON.readTree(json), words);

        assertFalse(words.contains("keyed_overwrite_cases_unmeasured"), words::toString);
    }

    /**
     * A map filed from a list that no decision looks a value up in says nothing of the order of
     * its repeated keys: how many entries it holds does not turn on which of several elements of a
     * key is the last.
     */
    @Test
    void aMapFiledFromAListNoDecisionLooksUpIsSaidNothingOf() throws Exception {
        Compilation compilation = measured("""
                module p
                data Row = { sku: String, qty: Int }
                behavior f : (rows: List<Row>) -> Bool
                let f (rows) = Map.size(List.indexBy(.sku, rows)) >= 2
                """);
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
        List<String> words = new ArrayList<>();
        collectWeakening(JSON.readTree(json), words);

        assertFalse(words.contains("keyed_overwrite_cases_unmeasured"), words::toString);
    }

    /**
     * A list whose rules keep its elements apart at the key holds no key twice, so every element
     * is the entry of its key and the order of a repeated key is no case of the model. Beside
     * {@link #MODEL}, which differs by the invariant alone.
     */
    @Test
    void aListWhoseRulesKeepTheKeysApartHasNoOrderToMeasure() throws Exception {
        Compilation compilation = measured("""
                module p
                data LI = { sku: String, q: Int }
                data Row = { sku: String, qty: Int }
                data Rows = { rows: List<Row> }
                    invariant List.allDistinctBy(.sku, rows)
                data Empty = { n: Int }
                behavior f : (items: List<LI>, snap: Rows) -> Int | Empty
                let f (items, snap) = {
                    let stock = List.indexBy(.sku, snap.rows)
                    guard List.all(i -> match Map.get(i.sku, stock) with
                        | Some r -> r.qty >= i.q
                        | None -> i.q <= 0, items) else Empty { n = 0 }
                    1
                }
                """);
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
        List<String> words = new ArrayList<>();
        collectWeakening(JSON.readTree(json), words);

        assertFalse(words.contains("keyed_overwrite_cases_unmeasured"), words::toString);
        assertFalse(json.contains("last snap.rows"), json);
        assertTrue(readSaveForWhatTheOtherValueReaches(report(compilation)),
                () -> report(compilation));
    }

    /**
     * The same of a list a dependency answers: the rules of what it answers hold of every answer.
     * Beside it, the same dependency answering a list nothing keeps apart is still said to leave the
     * order unmeasured.
     */
    @Test
    void aDependencysListWhoseRulesKeepTheKeysApartHasNoOrderToMeasure() throws Exception {
        String model = """
                module p
                data LI = { sku: String, q: Int }
                data Row = { sku: String, qty: Int }
                data Rows = { rows: List<Row> }
                    %s
                data Empty = { n: Int }
                behavior readRows : (items: List<LI>) -> Rows
                    constructs Rows, Row
                behavior f : (items: List<LI>) -> Int | Empty
                    depends on readRows
                let f (items, readRows) = {
                    let stock = List.indexBy(.sku, readRows(items).rows)
                    guard List.all(i -> match Map.get(i.sku, stock) with
                        | Some r -> r.qty >= i.q
                        | None -> i.q <= 0, items) else Empty { n = 0 }
                    1
                }
                """;
        List<String> apart = new ArrayList<>();
        Compilation kept = measured(model.formatted("invariant List.allDistinctBy(.sku, rows)"));
        collectWeakening(JSON.readTree(AdequacyReport.of(kept)
                .json(SourceRendering.namedByIdentity(kept.texts()))), apart);
        List<String> mayRepeat = new ArrayList<>();
        Compilation open = measured(model.formatted("invariant List.length(rows) >= 0"));
        collectWeakening(JSON.readTree(AdequacyReport.of(open)
                .json(SourceRendering.namedByIdentity(open.texts()))), mayRepeat);

        assertEquals(List.of(), errors(kept));
        assertFalse(apart.contains("keyed_overwrite_cases_unmeasured"), apart::toString);
        assertTrue(mayRepeat.contains("keyed_overwrite_cases_unmeasured"), mayRepeat::toString);
    }

    private static void collectWeakening(JsonNode node, List<String> into) {
        if (node.isObject()) {
            node.properties().forEach(entry -> {
                if (entry.getKey().equals("weakening") && entry.getValue().isArray()) {
                    entry.getValue().forEach(each -> into.add(each.asString()));
                }
                collectWeakening(entry.getValue(), into);
            });
        } else if (node.isArray()) {
            node.forEach(each -> collectWeakening(each, into));
        }
    }

    /**
     * The decisions the guard states, written as rows with the answers the definition gives: the
     * later of two rows of a key is the one looked up, so the same two rows the other way round
     * answer the other way.
     */
    @Test
    void theLastRowOfAKeyIsTheOneLookedUp() {
        Compilation compilation = measured(MODEL + """

                example f
                    | "no items" : ([], [Row { sku = "A", qty = 1 }]) -> 1
                    | "key not filed, threshold above" : ([LI { sku = "A", q = 5 }], []) -> Empty { n = 0 }
                    | "key not filed, nothing wanted" : ([LI { sku = "A", q = 0 }], []) -> 1
                    | "last row short" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 2 }]) -> Empty { n = 0 }
                    | "last row enough" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 2 }, Row { sku = "A", qty = 10 }]) -> 1
                    | "another key holds the quantity" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 2 }, Row { sku = "B", qty = 20 }]) -> Empty { n = 0 }
                    | "on the line" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 5 }]) -> 1
                    | "under the line" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 4 }]) -> Empty { n = 0 }
                """);

        assertEquals(List.of(), errors(compilation), () -> report(compilation));
    }

    /** Weakening words of a model measured with {@code rows} written for it. */
    private static List<String> weakeningWith(String rows) throws Exception {
        Compilation compilation = measured(MODEL + "\nexample f\n" + rows);
        assertEquals(List.of(), errors(compilation), () -> report(compilation));
        List<String> words = new ArrayList<>();
        collectWeakening(JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()))), words);
        return words;
    }

    /**
     * Rows where the order of a key held twice decided the guard both ways round — the last row
     * short where the first was enough, and the last enough where the first was short — leave
     * nothing of the order unmeasured.
     */
    @Test
    void rowsWhereTheOrderDecidedBothWaysMeasureIt() throws Exception {
        List<String> words = weakeningWith("""
                    | "last row short" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 2 }]) -> Empty { n = 0 }
                    | "last row enough" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 2 }, Row { sku = "A", qty = 10 }]) -> 1
                """);

        assertFalse(words.contains("keyed_overwrite_cases_unmeasured"), words::toString);
    }

    /**
     * The control: rows of one way round only, and rows holding a key twice where the order
     * decides nothing, leave the other way unmeasured.
     */
    @Test
    void rowsWhereTheOrderDecidedOneWayLeaveTheOtherUnmeasured() throws Exception {
        List<String> oneWay = weakeningWith("""
                    | "last row short" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 2 }]) -> Empty { n = 0 }
                """);
        List<String> decidingNothing = weakeningWith("""
                    | "both short" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 1 }, Row { sku = "A", qty = 2 }]) -> Empty { n = 0 }
                    | "both enough" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 20 }]) -> 1
                """);

        assertTrue(oneWay.contains("keyed_overwrite_cases_unmeasured"), oneWay::toString);
        assertTrue(decidingNothing.contains("keyed_overwrite_cases_unmeasured"),
                decidingNothing::toString);
    }

    /** Weakening words of {@code source} measured as it stands, which must have no error. */
    private static List<String> weakeningOf(String source) throws Exception {
        Compilation compilation = measured(source);
        assertEquals(List.of(), errors(compilation), () -> report(compilation));
        List<String> words = new ArrayList<>();
        collectWeakening(JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()))), words);
        return words;
    }

    /** The lookup decides only where {@code enabled}; elsewhere the behavior answers 0 and the
     *  lookup is never made. */
    private static final String GUARDED = """
            module p
            data LI = { sku: String, q: Int }
            data Row = { sku: String, qty: Int }
            behavior f : (enabled: Bool, items: List<LI>, rows: List<Row>) -> Int
            let enough (stock: Map<String, Row>, i: LI): Bool =
                match Map.get(i.sku, stock) with
                    | Some r -> r.qty >= i.q
                    | None -> i.q <= 0
            let f (enabled, items, rows) = {
                let stock = List.indexBy(.sku, rows)
                if enabled then (if List.all(i -> enough(stock, i), items) then 1 else 2) else 0
            }
            example f
            """;

    private static final String BOTH_SIDES_OF_THE_GUARD = """
                | "enough" : (true, [LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 10 }]) -> 1
                | "short" : (true, [LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 2 }]) -> 2
            """;

    /**
     * A row is evidence about a decision where its run went through it. Rows that hold a key twice
     * in both orders, but with the lookup switched off, are inputs the lookup would tell apart and
     * were never asked: the order of the repeated key stays unmeasured.
     */
    @Test
    void rowsThatNeverReachedTheLookupDoNotMeasureItsOrder() throws Exception {
        List<String> words = weakeningOf(GUARDED + BOTH_SIDES_OF_THE_GUARD + """
                | "off, last short" : (false, [LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 2 }]) -> 0
                | "off, last enough" : (false, [LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 2 }, Row { sku = "A", qty = 10 }]) -> 0
                """);

        assertTrue(words.contains("keyed_overwrite_cases_unmeasured"), words::toString);
    }

    /** The control: the same two orders with the lookup switched on measure it. */
    @Test
    void rowsThatRanThroughTheLookupMeasureItsOrder() throws Exception {
        List<String> words = weakeningOf(GUARDED + BOTH_SIDES_OF_THE_GUARD + """
                | "on, last short" : (true, [LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 2 }]) -> 2
                | "on, last enough" : (true, [LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 2 }, Row { sku = "A", qty = 10 }]) -> 1
                """);

        assertFalse(words.contains("keyed_overwrite_cases_unmeasured"), words::toString);
    }

    /** One decision resting on the entries of two maps, each filed from a list of its own. */
    private static final String TWO_MAPS = """
            module p
            data LI = { sku: String, q: Int }
            data Row = { sku: String, qty: Int }
            data Empty = { n: Int }
            behavior f : (items: List<LI>, a: List<Row>, b: List<Row>) -> Int | Empty
            let have (stock: Map<String, Row>, i: LI): Bool =
                match Map.get(i.sku, stock) with
                    | Some r -> r.qty >= i.q
                    | None -> false
            let f (items, a, b) = {
                let sa = List.indexBy(.sku, a)
                let sb = List.indexBy(.sku, b)
                guard List.all(i -> have(sa, i) || have(sb, i), items) else Empty { n = 0 }
                1
            }
            example f
            """;

    /**
     * Each order is its own distinction. Rows that settle the order of the first map both ways say
     * nothing of the second, whose order no row has been asked about.
     */
    @Test
    void theOrderOfOneMapIsNotTheOrderOfAnother() throws Exception {
        List<String> words = weakeningOf(TWO_MAPS + """
                | "first, last short" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 2 }], []) -> Empty { n = 0 }
                | "first, last enough" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 2 }, Row { sku = "A", qty = 10 }], []) -> 1
                """);

        assertTrue(words.contains("keyed_overwrite_cases_unmeasured"), words::toString);
    }

    /**
     * And each is measured on its own: in rows where both maps hold a key twice, reading both the
     * other way round changes nothing — one makes the answer what the other undoes — while reading
     * either alone does. Four such rows settle both orders both ways.
     */
    @Test
    void eachOrderIsMeasuredWithTheOtherLeftAsItIs() throws Exception {
        List<String> words = weakeningOf(TWO_MAPS + """
                | "second decides, held" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 2 }], [Row { sku = "A", qty = 2 }, Row { sku = "A", qty = 10 }]) -> 1
                | "first decides, held" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 2 }, Row { sku = "A", qty = 10 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 2 }]) -> 1
                | "first decides, failed" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 2 }], [Row { sku = "A", qty = 2 }]) -> Empty { n = 0 }
                | "second decides, failed" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 2 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 2 }]) -> Empty { n = 0 }
                """);

        assertFalse(words.contains("keyed_overwrite_cases_unmeasured"), words::toString);
    }

    /** The control: a wrong answer for the repeated key is refused. */
    @Test
    void anAnswerTheLookupDoesNotGiveIsRefused() {
        Compilation compilation = measured(MODEL + """

                example f
                    | "last row short" : ([LI { sku = "A", q = 5 }], [Row { sku = "A", qty = 10 }, Row { sku = "A", qty = 2 }]) -> 1
                """);

        assertFalse(errors(compilation).isEmpty(), () -> report(compilation));
    }

    private static final String ENOUGH = """
            module p
            data Row = { sku: String, qty: Int }
            behavior f : (k: String, rows: List<Row>) -> Bool
            let f (k, rows) =
                match Map.get(k, List.indexBy(.sku, rows)) with
                    | Some r -> r.qty >= 5
                    | None -> false
            """;

    /** The points of the line this row leaves undecided, by the word the report uses. */
    private static List<String> undecidedAfter(String rows) {
        List<String> out = new ArrayList<>();
        for (String line : report(measured(ENOUGH + """

                example f
                    | "duplicated key" : ("A", %s) -> true
                """.formatted(rows))).lines().toList()) {
            Matcher point = Pattern.compile("no row is at (?:the|an) (\\w+) point")
                    .matcher(line);
            if (point.find()) {
                out.add(point.group(1));
            }
        }
        return out;
    }

    /**
     * Whether a row stands at a point of a line is asked of the element the lookup answers: the
     * last of the key. Two rows of one key stand at the point the last of them is at — on the line
     * where the later holds five, above it where the later holds nine — whatever the earlier holds.
     */
    @Test
    void aRowStandsAtALineWhereTheLastRowOfItsKeyDoes() {
        List<String> lastOnTheLine =
                undecidedAfter("[Row { sku = \"A\", qty = 9 }, Row { sku = \"A\", qty = 5 }]");
        List<String> lastAboveTheLine =
                undecidedAfter("[Row { sku = \"A\", qty = 5 }, Row { sku = \"A\", qty = 9 }]");

        assertEquals(List.of("OFF", "IN", "OUT"), lastOnTheLine);
        assertEquals(List.of("ON", "OFF", "OUT"), lastAboveTheLine);
    }

    private static final Pattern ITEM =Pattern.compile("LI \\{ sku = \"([^\"]*)\", q = (-?\\d+) \\}");

    private static final Pattern ROW = Pattern.compile("Row \\{ sku = \"([^\"]*)\", qty = (-?\\d+) \\}");

    private static List<String[]> found(Pattern kind, String text) {
        List<String[]> out = new ArrayList<>();
        Matcher each = kind.matcher(text);
        while (each.find()) {
            out.add(new String[] {each.group(1), each.group(2)});
        }
        return out;
    }

    /**
     * Every row offered for a point is answered by what the definition gives and run: the rows
     * stand at the lines they were offered for, or the examples would be refused or leave an
     * obligation unmet.
     */
    @Test
    void theRowsOfferedAreAnsweredByTheDefinitionAndMeetEveryBorder() {
        Compilation compilation = measured(MODEL);
        Generator.GenerationResult offered =
                OfferedAtTheLines.of(compilation, compilation.modules().get(0), "f");
        assertEquals(List.of(), offered.unresolved(), "every point is offered a row");
        assertEquals(8, offered.rows().size(), () -> offered.rows().toString());

        StringBuilder examples = new StringBuilder("\nexample f\n");
        int number = 0;
        for (Generator.GeneratedRow row : offered.rows()) {
            List<FixtureTemplate> inputs = row.inputs();
            boolean admitted = admits(found(ITEM, inputs.get(0).text()),
                    found(ROW, inputs.get(1).text()));
            examples.append("    | \"row ").append(++number).append("\" : (")
                    .append(inputs.get(0).text()).append(", ").append(inputs.get(1).text())
                    .append(") -> ").append(admitted ? "1" : "Empty { n = 0 }").append('\n');
        }
        Compilation answered = measured(MODEL + examples);

        assertEquals(List.of(), errors(answered), () -> examples + report(answered));
        assertTrue(report(answered).contains("obligations 8/8"), () -> report(answered));
    }
}
