package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior whose weakening names a case no row was seen in, or a weight nothing decided, says
 * which one on the page and in the document, and not only that the measure is partial.
 *
 * <p>The words published for these are {@code reachable_node_cases_unmeasured},
 * {@code keyed_overwrite_cases_unmeasured} and {@code a_weight_not_decided}. Each is asked of the
 * text a reader is handed and of the document a consumer is, and the two are asked of the same
 * models, so that one saying what the other does not is a failure here.
 */
class APartialMeasureSaysWhatItWentWithoutOnThePageTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String SEARCH = """
            module m
            data Node = { v: Int, below: List<Node> }
            data Yes
            data No
            let anyBig (n: Node): Bool = n.v > 5 || List.any(c -> anyBig(c), n.below)
            behavior f : (t: Node) -> Yes | No
            let f (t) = if anyBig(t) then Yes else No
            example f
                | "the top" : (Node { v = 9, below = [] }) -> Yes
                | "nothing below" : (Node { v = 0, below = [] }) -> No
            """;

    private static final String TWO_SEARCHES = """
            module m
            data Node = { v: Int, below: List<Node> }
            data Yes
            data No
            let anyBig (n: Node): Bool = n.v > 5 || List.any(c -> anyBig(c), n.below)
            let anyHuge (n: Node): Bool = n.v > 50 || List.any(c -> anyHuge(c), n.below)
            behavior f : (t: Node) -> Yes | No
            let f (t) = if anyBig(t) then Yes else if anyHuge(t) then Yes else No
            example f
                | "a" : (Node { v = 9, below = [] }) -> Yes
            """;

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
            """;

    private static final String KEYED = """
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

    private static final String WEIGHTS = """
            module example.it
            data Row = { grade: Int, lowerBound: Int }
            data Yen = Int
                invariant value >= 0
            data Rem = { base: Yen, extra: Yen }
            let table: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                     Row { grade = 2, lowerBound = 100 },
                                     Row { grade = 3, lowerBound = 200 } ]
            let gradeOf (m: Int): Int =
                List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 1, table)
            behavior g : (r: Rem) -> Int
            let g (r) = gradeOf(r.base.value + r.extra.value)
            """;

    /** A page and a document of one model, measured and answered in full. */
    private record Report(String human, String japanese, JsonNode document) {

        /** Each model is measured once for the four tests that read it. */
        private static final Map<String, Report> MEASURED = new ConcurrentHashMap<>();

        static Report of(String source) {
            return MEASURED.computeIfAbsent(source, Report::measure);
        }

        private static Report measure(String source) {
            Compilation compilation = ACompiledModel.measured(source, Adequacy.Asked.fullReport());
            SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());
            AdequacyReport report = AdequacyReport.of(compilation);
            return new Report(report.humanInEnglish(rendering),
                    report.human(rendering, Locale.JAPANESE),
                    JSON.readTree(report.json(rendering)));
        }

        List<String> weakeningWords() {
            List<String> out = new ArrayList<>();
            collect(document, out);
            return out;
        }

        private static void collect(JsonNode node, List<String> into) {
            if (node.isObject()) {
                node.properties().forEach(each -> {
                    if (each.getKey().equals("weakening") && each.getValue().isArray()) {
                        each.getValue().forEach(word -> into.add(word.asString()));
                    }
                    collect(each.getValue(), into);
                });
            } else if (node.isArray()) {
                node.forEach(one -> collect(one, into));
            }
        }

        /** The statements the decision lacks cases of, in the order the page numbers them. */
        JsonNode statements() {
            List<JsonNode> found = fieldsNamed("statementsNoRowIsIn");
            assertEquals(1, found.size(), "one behavior, one decision");
            return found.getFirst();
        }

        /** Every object under the document that has the field, in document order. */
        List<JsonNode> fieldsNamed(String name) {
            List<JsonNode> out = new ArrayList<>();
            find(document, name, out);
            return out;
        }

        private static void find(JsonNode node, String name, List<JsonNode> into) {
            if (node.isObject()) {
                node.properties().forEach(each -> {
                    if (each.getKey().equals(name)) {
                        into.add(each.getValue());
                    }
                    find(each.getValue(), name, into);
                });
            } else if (node.isArray()) {
                node.forEach(one -> find(one, name, into));
            }
        }
    }

    @Test
    void aSearchStepNoRowIsInIsNamedOnThePageAndInTheDocument() throws Exception {
        Report report = Report.of(SEARCH);

        assertTrue(report.weakeningWords().contains("reachable_node_cases_unmeasured"),
                report.weakeningWords()::toString);
        assertTrue(report.human().contains("      ? no row is in these cases of statement 1,"
                + " a search from t through below, written at " + positionOf(SEARCH, "anyBig(t)")
                + ":\n"
                + "          · the node does not and one below it does\n"
                + "          · the node does not and every node below it comes back empty\n"),
                report.human());
        assertFalse(report.human().contains("the node meets what it asks"), report.human());
        JsonNode statements = report.statements();
        assertEquals(1, statements.size());
        assertEquals("a_node_a_search_reaches", statements.get(0).get("kind").asString());
        assertTrue(statements.get(0).get("askable").asBoolean());
        assertEquals(List.of("below_it", "nowhere_below"), words(statements.get(0).get("cases")));
    }

    /** Where the first {@code text} is written in {@code source}, as the page says a place. */
    private static String positionOf(String source, String text) {
        String[] lines = source.split("\n");
        for (int line = 0; line < lines.length; line++) {
            int column = lines[line].indexOf(text);
            if (column >= 0) {
                return (line + 1) + ":" + (column + 1);
            }
        }
        throw new IllegalArgumentException(text + " is not written in the source");
    }

    private static List<String> words(JsonNode array) {
        List<String> out = new ArrayList<>();
        array.forEach(each -> out.add(each.asString()));
        return out;
    }

    /**
     * Two searches from one place through one field are two statements. Said by where they start
     * and what they go through alone they read alike, so each is said by where its condition is
     * written: the call of {@code anyBig} and the call of {@code anyHuge}.
     */
    @Test
    void twoSearchesFromOnePlaceThroughOneFieldAreToldApartByWhereTheyAreWritten()
            throws Exception {
        Report report = Report.of(TWO_SEARCHES);

        assertTrue(report.human().contains("? no row is in these cases of statement 1, a search"
                + " from t through below, written at " + positionOf(TWO_SEARCHES, "anyBig(t)")
                + ":"), report.human());
        assertTrue(report.human().contains("? no row is in these cases of statement 2, a search"
                + " from t through below, written at " + positionOf(TWO_SEARCHES, "anyHuge(t)")
                + ":"), report.human());
        assertTwoDifferentStatements(report);
    }

    /** One statement resting on two maps: it is one place and two orders, told apart by the
     *  container whose elements the order is of. */
    @Test
    void twoOrdersUnderOneStatementAreToldApartByTheirContainers() throws Exception {
        Report report = Report.of(TWO_MAPS);
        String written = ", written at " + positionOf(TWO_MAPS, "List.all(") + ":\n";

        assertTrue(report.human().contains("statement 1, the order of the elements of a that share"
                + " a a[*].sku" + written + "          · the statement holds with the last of"
                + " them"), report.human());
        assertTrue(report.human().contains("statement 2, the order of the elements of b that share"
                + " a b[*].sku" + written + "          · the statement holds with the last of"
                + " them"), report.human());
        assertTwoDifferentStatements(report);
    }

    /** What the page numbers 1 and 2 are two entries of the document, and are not one spelled
     *  twice. */
    private static void assertTwoDifferentStatements(Report report) {
        JsonNode statements = report.statements();
        assertEquals(2, statements.size(), statements::toString);
        assertFalse(statements.get(0).get("statement").asString()
                .equals(statements.get(1).get("statement").asString()), statements::toString);
    }

    @Test
    void theOrderOfARepeatedKeyNoRowIsInIsNamedOnThePageAndInTheDocument() throws Exception {
        Report report = Report.of(KEYED);

        assertTrue(report.weakeningWords().contains("keyed_overwrite_cases_unmeasured"),
                report.weakeningWords()::toString);
        assertTrue(report.human().contains("      ? no row is in these cases of statement 1, the"
                + " order of the elements of rows that share a rows[*].sku, written at "
                + positionOf(KEYED, "List.all(") + ":\n"
                + "          · the statement holds with the last of them and fails with an earlier"
                + " one\n          · the statement fails with the last of them and holds with an"
                + " earlier one\n"), report.human());
        JsonNode statements = report.statements();
        assertEquals(1, statements.size());
        assertEquals("the_order_of_a_repeated_key", statements.get(0).get("kind").asString());
        assertEquals(List.of("holds_by_the_last", "fails_by_the_last"),
                words(statements.get(0).get("cases")));
    }

    @Test
    void theWeightsNothingDecidedAreNamedOnThePageWithTheirReasonAndInTheDocument()
            throws Exception {
        Report report = Report.of(WEIGHTS);

        assertTrue(report.weakeningWords().contains("a_weight_not_decided"),
                report.weakeningWords()::toString);
        assertTrue(report.human().contains("      ? not decided whether the rows fix how these"
                + " positions weigh into `r.base + r.extra`\n          · r.base\n"
                + "          · r.extra\n          because a border of it was not read in full\n"),
                report.human());
        List<String> reasons = new ArrayList<>();
        report.fieldsNamed("undecidedBecause")
                .forEach(each -> each.forEach(why -> reasons.add(why.asString())));
        assertEquals(List.of("a_border_was_not_read_in_full", "a_border_was_not_read_in_full"),
                reasons);
        // Whatever an undecided weight is undecided for, the document says it: its own reasons,
        // what its borders went without, or both. Never neither.
        for (JsonNode weights : report.fieldsNamed("weights")) {
            weights.forEach(weight -> {
                if (weight.get("standing").asString().equals("undecided")) {
                    assertTrue(weight.has("undecidedBecause") || weight.has("weakening"),
                            weight::toString);
                }
            });
        }
    }

    /**
     * The same three words, asked of every model above: where the document publishes one of them,
     * the page has a line for it and the document has the detail beside it, and the page is said in
     * the other language as well.
     */
    @Test
    void aWordPublishedForAWeakeningHasALineOnThePageAndTheDetailInTheDocument() throws Exception {
        Map<String, String> sourceOf = Map.of("search", SEARCH, "keyed", KEYED, "weights", WEIGHTS);
        Map<String, List<String>> lineFor = Map.of(
                "reachable_node_cases_unmeasured",
                        List.of("? no row is in these cases of statement 1, a search"),
                "keyed_overwrite_cases_unmeasured",
                        List.of("? no row is in these cases of statement 1, the order"),
                "a_weight_not_decided", List.of("? not decided whether the rows fix how"));
        Map<String, String> detailFor = Map.of(
                "reachable_node_cases_unmeasured", "statementsNoRowIsIn",
                "keyed_overwrite_cases_unmeasured", "statementsNoRowIsIn",
                "a_weight_not_decided", "undecidedBecause");
        Set<String> checked = new TreeSet<>();
        for (Map.Entry<String, String> model : sourceOf.entrySet()) {
            Report report = Report.of(model.getValue());
            for (String word : new TreeSet<>(report.weakeningWords())) {
                if (!lineFor.containsKey(word)) {
                    continue;
                }
                checked.add(word);
                assertTrue(lineFor.get(word).stream().allMatch(report.human()::contains),
                        () -> model.getKey() + " publishes " + word + " and the page says nothing"
                                + " of it:\n" + report.human());
                assertFalse(report.fieldsNamed(detailFor.get(word)).isEmpty(),
                        () -> model.getKey() + " publishes " + word + " with no "
                                + detailFor.get(word));
                assertFalse(report.japanese().contains("report."),
                        () -> "a message left without its words:\n" + report.japanese());
            }
        }
        assertEquals(lineFor.keySet(), checked, "each model publishes the word it is built to");
    }
}
