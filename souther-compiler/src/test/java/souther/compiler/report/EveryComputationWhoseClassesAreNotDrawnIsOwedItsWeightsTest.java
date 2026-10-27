package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The positions of a computation cut at several places are divided by none of its thresholds and
 * are owed a weight each, and these are one decision: where the classes are not drawn the weights
 * are owed, whatever the rows are, and the document says where each stands.
 */
class EveryComputationWhoseClassesAreNotDrawnIsOwedItsWeightsTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String DECLARATIONS = """
            module demo

            data N = { v: Int }
                invariant v >= 0
            data Row = { grade: Int, lowerBound: Int }
            let table: List<Row> = [ Row { grade = 2, lowerBound = 100 },
                                     Row { grade = 3, lowerBound = 200 } ]
            let gradeOf (m: Int): Int =
                List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 1, table)

            behavior f : (a: N, b: N) -> Int

            """;

    private static final String ONE_CALL = DECLARATIONS + """
            let f (a, b) =
                gradeOf(a.v + b.v)
            """;

    private static final String TWO_CALLS = DECLARATIONS + """
            let f (a, b) =
                gradeOf(a.v + b.v) + gradeOf(a.v + 3 * b.v)
            """;

    private static final String A_ROW_OFF_EVERY_BORDER = """

            example f
                | (N { v = 1 }, N { v = 1 }) -> 1
            """;

    private static final String A_ROW_OFF_EVERY_BORDER_OF_TWO_CALLS = """

            example f
                | (N { v = 1 }, N { v = 1 }) -> 2
            """;

    /** The positions have no class from the thresholds and the document owes each its weight. */
    @Test
    void aPositionWithNoClassOfItsOwnIsOwedItsWeight() {
        JsonNode partition = partitionOf(ONE_CALL + A_ROW_OFF_EVERY_BORDER);
        assertTrue(axesPaths(partition).isEmpty(), () -> "no class from the table: " + partition);
        assertEquals(List.of("a.v", "b.v"), positionsOf(weightsOf(partition)));
    }

    /** Where nothing was read against the computation the weights are still owed, and the
     *  document says they are undecided rather than leaving them out. */
    @Test
    void aComputationNothingWasReadAgainstIsStillOwedItsWeightsAndSaysUndecided() {
        JsonNode partition = partitionOf(ONE_CALL);
        assertTrue(axesPaths(partition).isEmpty(), () -> "no class from the table: " + partition);
        List<JsonNode> weights = weightsOf(partition);
        assertEquals(List.of("a.v", "b.v"), positionsOf(weights));
        weights.forEach(each -> assertEquals("undecided", each.get("standing").asString()));
    }

    /** One comparison read at two calls is two computations, told apart in the identity. */
    @Test
    void theSameComparisonAtTwoCallsIsTwoComputationsInTheDocument() {
        List<JsonNode> weights =
                weightsOf(partitionOf(TWO_CALLS + A_ROW_OFF_EVERY_BORDER_OF_TWO_CALLS));
        assertEquals(4, weights.size(), () -> "a weight for each position of each: " + weights);
        List<JsonNode> computations = weights.stream()
                .map(each -> each.get("obligationId").get("copies")).distinct().toList();
        assertEquals(2, computations.size(), () -> "two computations: " + weights);
        assertNotEquals(computations.get(0), computations.get(1));
        assertEquals(weights.stream().map(each -> each.get("obligationId")).distinct().count(),
                weights.size(), "no two weights share an identity");
    }

    /** One value handed to two calls is one computation, cut at the same places by both: the rows
     *  on the borders are the same rows, and each position is owed its weight once. */
    @Test
    void oneValueHandedToTwoCallsIsOneComputation() {
        List<JsonNode> weights = weightsOf(partitionOf(DECLARATIONS + """
                let f (a, b) = {
                    let m = a.v + b.v
                    gradeOf(m) + gradeOf(m)
                }
                """ + A_ROW_OFF_EVERY_BORDER_OF_TWO_CALLS));
        assertEquals(2, weights.size(), () -> "a weight for each position, once: " + weights);
        weights.forEach(each -> assertEquals(2, each.get("obligationId").get("copies").size(),
                () -> "both calls are the one computation: " + each));
    }

    /** Every finding about a weight joins the entry that carries the same identity. */
    @Test
    void aFindingAboutAWeightJoinsItsEntry() {
        JsonNode document = documentOf(ONE_CALL + A_ROW_OFF_EVERY_BORDER);
        List<JsonNode> weights = weightsOf(document.get("modules").get(0).get("behaviors").get(0)
                .get("partition"));
        List<JsonNode> findings = new ArrayList<>();
        collect(document, "tilt_of_a_derived_value_not_shown", findings);
        assertFalse(findings.isEmpty(), "rows off every border fix nothing");
        for (JsonNode finding : findings) {
            assertEquals(1, weights.stream().filter(each -> each.get("obligationId")
                    .equals(finding.get("obligationId"))).count(),
                    () -> "one entry for " + finding.get("obligationId"));
        }
    }

    /** And the document is one the schema describes. */
    @Test
    void theDocumentIsShapedLikeTheSchema() {
        DocumentShape.assertShapedLikeTheSchema(
                documentOf(TWO_CALLS + A_ROW_OFF_EVERY_BORDER_OF_TWO_CALLS));
    }

    private static void collect(JsonNode at, String kind, List<JsonNode> into) {
        if (at.isObject() && at.has("kind") && kind.equals(at.get("kind").asString())) {
            into.add(at);
        }
        at.forEach(child -> collect(child, kind, into));
    }

    private static List<String> axesPaths(JsonNode partition) {
        List<String> out = new ArrayList<>();
        partition.get("axes").forEach(each -> out.add(each.get("path").asString()));
        return out;
    }

    private static List<JsonNode> weightsOf(JsonNode partition) {
        List<JsonNode> out = new ArrayList<>();
        if (partition.has("weights")) {
            partition.get("weights").forEach(out::add);
        }
        return out;
    }

    private static List<String> positionsOf(List<JsonNode> weights) {
        return weights.stream().map(each -> each.get("obligationId").get("position").asString())
                .distinct().sorted().toList();
    }

    private static JsonNode partitionOf(String source) {
        return documentOf(source).get("modules").get(0).get("behaviors").get(0).get("partition");
    }

    private static JsonNode documentOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "a model that did not compile: "
                + compilation.errors());
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
    }
}
