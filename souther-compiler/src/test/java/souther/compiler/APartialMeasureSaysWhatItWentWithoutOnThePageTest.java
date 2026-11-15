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

        static Report of(String source) throws Exception {
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
        assertTrue(report.human().contains("      ? no row is in the case of the search from t"
                + " through below where the node does not and one below it does"), report.human());
        assertTrue(report.human().contains("where the node does not and every node below it comes"
                + " back empty"), report.human());
        assertFalse(report.human().contains("where the node meets what it asks"), report.human());
        List<JsonNode> cases = report.fieldsNamed("casesNotSeen");
        assertEquals(1, cases.size());
        List<String> steps = new ArrayList<>();
        cases.getFirst().forEach(each -> {
            assertEquals("search_step", each.get("kind").asString());
            assertEquals("t", each.get("from").asString());
            assertEquals("below", each.get("through").get(0).asString());
            steps.add(each.get("step").asString());
        });
        assertEquals(List.of("below_it", "nowhere_below"), steps);
    }

    @Test
    void theOrderOfARepeatedKeyNoRowIsInIsNamedOnThePageAndInTheDocument() throws Exception {
        Report report = Report.of(KEYED);

        assertTrue(report.weakeningWords().contains("keyed_overwrite_cases_unmeasured"),
                report.weakeningWords()::toString);
        assertTrue(report.human().contains("      ? no row is in the case of the order of the"
                + " elements of rows that share a rows[*].sku, where the statement holds with the"
                + " last of them and fails with an earlier one"), report.human());
        assertTrue(report.human().contains("where the statement fails with the last of them and"
                + " holds with an earlier one"), report.human());
        List<JsonNode> cases = report.fieldsNamed("casesNotSeen");
        assertEquals(1, cases.size());
        assertEquals("key_order", cases.getFirst().get(0).get("kind").asString());
        assertEquals("rows", cases.getFirst().get(0).get("container").asString());
        assertEquals("rows[*].sku", cases.getFirst().get(0).get("position").asString());
        assertEquals(List.of("holds_by_the_last", "fails_by_the_last"), cases.getFirst()
                .valueStream().map(each -> each.get("way").asString()).toList());
    }

    @Test
    void theWeightsNothingDecidedAreNamedOnThePageWithTheirReasonAndInTheDocument()
            throws Exception {
        Report report = Report.of(WEIGHTS);

        assertTrue(report.weakeningWords().contains("a_weight_not_decided"),
                report.weakeningWords()::toString);
        assertTrue(report.human().contains("      ? not decided whether the rows fix how these"
                + " positions weigh into `r.base + r.extra` — a border of it was not read in full"),
                report.human());
        assertTrue(report.human().contains("          · r.base"), report.human());
        assertTrue(report.human().contains("          · r.extra"), report.human());
        List<String> reasons = new ArrayList<>();
        report.fieldsNamed("undecidedBecause")
                .forEach(each -> each.forEach(why -> reasons.add(why.asString())));
        assertEquals(List.of("a_border_was_not_read_in_full", "a_border_was_not_read_in_full"),
                reasons);
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
                "reachable_node_cases_unmeasured", List.of("? no row is in the case of the search"),
                "keyed_overwrite_cases_unmeasured", List.of("? no row is in the case of the order"),
                "a_weight_not_decided", List.of("? not decided whether the rows fix how"));
        Map<String, String> detailFor = Map.of(
                "reachable_node_cases_unmeasured", "casesNotSeen",
                "keyed_overwrite_cases_unmeasured", "casesNotSeen",
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
