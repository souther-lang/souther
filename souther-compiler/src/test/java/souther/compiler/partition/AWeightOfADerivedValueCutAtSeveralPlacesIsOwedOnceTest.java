package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A weight is a fault of the computation, which every threshold of its table reads, so a value cut
 * at several places owes it once and not again beside each threshold.
 */
class AWeightOfADerivedValueCutAtSeveralPlacesIsOwedOnceTest {

    private static final String MODULE = """
            module example.it
            data Row = { grade: Int, lowerBound: Int }
            data Yen = Int
                invariant value >= 0
            data Rem = { base: Yen, extra: Yen }
            let table: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                     Row { grade = 2, lowerBound = 100 }%s ]
            let gradeOf (m: Int): Int =
                List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 1, table)
            behavior g : (r: Rem) -> Int
            let g (r) = gradeOf(r.base.value + r.extra.value)
            """;

    private static final String THIRD_BOUND = ",\n Row { grade = 3, lowerBound = 200 }";

    private static final String ROWS_AT_100 = """
            example g
                | "ON 100 in base"   : (Rem { base = Yen(100), extra = Yen(0) }) -> 2
                | "OFF 100 in base"  : (Rem { base = Yen(99), extra = Yen(0) }) -> 1
                | "IN in base"       : (Rem { base = Yen(150), extra = Yen(0) }) -> 2
                | "OUT in base"      : (Rem { base = Yen(50), extra = Yen(0) }) -> 1
            """;

    private static final String ROWS_AT_200 = """
                | "ON 200 in extra"  : (Rem { base = Yen(0), extra = Yen(200) }) -> 3
                | "OFF 200 in extra" : (Rem { base = Yen(0), extra = Yen(199) }) -> 2
            """;

    private static final String CUT_AT_TWO_PLACES = MODULE.formatted(THIRD_BOUND);

    private static final String CUT_AT_ONE_PLACE = MODULE.formatted("");

    /** The reproduction: the weight of each position is fixed by the rows, and nothing beside a
     *  threshold is asked about a weight again. */
    @Test
    void theWeightsAreOwedOnceAndNoBorderIsHeldAgainstALineThatWeighsAPositionOtherwise() {
        Document document = documentOf(CUT_AT_TWO_PLACES + ROWS_AT_100 + ROWS_AT_200);
        assertEquals(Map.of("r.base", "shown", "r.extra", "shown"), document.weights());
        assertEquals(List.of(), document.linesBeside());
        assertFalse(document.human().contains("no row tells"), document.human());
        assertEquals("satisfied", document.adequacy());
    }

    /** A weight the rows leave unfixed stays said, once for the position, and the borders are still
     *  not asked about it. */
    @Test
    void aWeightNoRowFixesIsStillOwedAndSaidOnce() {
        Document document = documentOf(CUT_AT_TWO_PLACES + ROWS_AT_100);
        assertEquals("not_shown", document.weights().get("r.extra"), document.weights().toString());
        assertEquals(2, document.weights().size(), document.weights().toString());
        assertEquals(List.of(), document.linesBeside());
        assertEquals(1, count(document.human(), "no row fixes how `r.extra` weighs"),
                document.human());
    }

    /** A value cut at one place is no computation shared by thresholds, so its border keeps the
     *  lines beside it and owes no weight. */
    @Test
    void aValueCutAtOnePlaceKeepsTheLinesBesideItsBorder() {
        Document document = documentOf(CUT_AT_ONE_PLACE + ROWS_AT_100);
        assertEquals(Map.of(), document.weights());
        assertFalse(document.linesBeside().isEmpty(), document.human());
        assertTrue(document.human().contains("no row tells"), document.human());
    }

    /** What the weights are short of reaches the verdict. Nothing is read against the
     *  computation here, so the weights are neither fixed nor shown unfixed, and the lines beside
     *  the thresholds are not where that is said. */
    @Test
    void aWeightTheRowsNeitherFixNorLeaveUnfixedIsWhatTheMeasureWentWithout() {
        assertTrue(documentOf(CUT_AT_TWO_PLACES).undecidedWeights() > 0);
        assertEquals(0, documentOf(CUT_AT_TWO_PLACES + ROWS_AT_100 + ROWS_AT_200)
                .undecidedWeights());
    }

    private static long count(String text, String word) {
        return text.lines().filter(each -> each.contains(word)).count();
    }

    /** What the report says of the module, read from the document and the human text. */
    private record Document(Map<String, String> weights, List<JsonNode> linesBeside,
                            long undecidedWeights, String adequacy, String human) {}

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static Document documentOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport report = AdequacyReport.of(compilation);
        JsonNode json = JSON.readTree(report.json(SourceRendering.namedByIdentity(
                compilation.texts())));
        Map<String, String> weights = new LinkedHashMap<>();
        List<JsonNode> besides = new ArrayList<>();
        long[] undecided = {0};
        walk(json, weights, besides, undecided);
        return new Document(weights, besides, undecided[0], json.get("adequacy").asString(),
                report.human(SourceRendering.namedByIdentity(compilation.texts())));
    }

    private static void walk(JsonNode node, Map<String, String> weights, List<JsonNode> besides,
                             long[] undecided) {
        if (node.isObject()) {
            node.properties().forEach(each -> {
                if (each.getKey().equals("weights") && each.getValue().isArray()) {
                    each.getValue().forEach(one -> weights.put(
                            one.get("obligationId").get("position").asString(),
                            one.get("standing").asString()));
                } else if (each.getKey().equals("besides") && each.getValue().isArray()) {
                    each.getValue().forEach(besides::add);
                }
                walk(each.getValue(), weights, besides, undecided);
            });
        } else if (node.isArray()) {
            node.forEach(one -> walk(one, weights, besides, undecided));
        } else if (node.isString() && node.asString().equals("a_weight_not_decided")) {
            undecided[0]++;
        }
    }
}
