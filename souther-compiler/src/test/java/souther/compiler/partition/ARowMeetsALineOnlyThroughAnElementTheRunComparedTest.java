package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row standing at a line drawn by a comparison inside a closure over the elements of an input
 * container meets it only through an element the run compared anything on.
 *
 * <p>{@code List.any} applies its closure to an element only where none before it held, so on
 * {@code [1, 0]} the comparison is made on the first element and never on the second. The run got
 * an answer out of the comparison, and a reading of the row through its second element stands at
 * {@code 0} — and nothing compared {@code 0}. {@code List.all} stops the other way round, and an
 * operation that applies its closure to every element compares each of them.
 */
class ARowMeetsALineOnlyThroughAnElementTheRunComparedTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module probe

            data Low
            data High

            behavior pick : (xs: List<Int>) -> Low | High
            let pick (xs) = if GUARD then High else Low
            """;

    private static final String NESTED = """
            module probe

            data Low
            data High

            behavior pick : (xss: List<List<Int>>) -> Low | High
            let pick (xss) = if GUARD then High else Low
            """;

    @Test
    void anOperationStoppingAtAHoldingAnswerComparesNothingAfterIt() {
        String guard = "List.any(x -> x > 0, xs)";
        assertFalse(hitAt(MODEL, guard, "([1, 0])", "0"),
                "the first element holds, and the second is never compared");
        assertTrue(hitAt(MODEL, guard, "([-1, 0])", "0"),
                "the first fails, so the second is compared");
    }

    @Test
    void anOperationStoppingAtAFailingAnswerComparesNothingAfterIt() {
        String guard = "List.all(x -> x > 0, xs)";
        assertFalse(hitAt(MODEL, guard, "([0, 1])", "1"),
                "the first element fails, and the second is never compared");
        assertTrue(hitAt(MODEL, guard, "([2, 1])", "1"),
                "the first holds, so the second is compared");
    }

    /** The control: the same comparison handed to an operation that applies it to every element. */
    @Test
    void anOperationOverEveryElementComparesEachOfThem() {
        assertTrue(hitAt(MODEL, "List.length(List.filter(x -> x > 0, xs)) >= 1", "([1, 0])", "0"),
                "the filter compares the second element whatever the first answered");
    }

    /**
     * Inside an element of an outer container, the inner container the run got to is that element's:
     * an inner element is compared where the outer operation got to its container and the inner one
     * got to it there.
     */
    @Test
    void anInnerElementIsComparedOnlyWhereTheOuterOperationGotToItsContainer() {
        String guard = "List.any(ys -> List.any(y -> y > 0, ys), xss)";
        assertFalse(hitAt(NESTED, guard, "([[1, 0], [0]])", "0"),
                "the first list holds at its first element: neither its second element nor the"
                        + " second list is compared");
        assertFalse(hitAt(NESTED, guard, "([[1], [0]])", "0"),
                "the first list holds, and the second is never compared");
        assertTrue(hitAt(NESTED, guard, "([[-1], [0]])", "0"),
                "the first list holds nowhere, so the second is compared");
    }

    /**
     * Over a container made of the input's, the operation goes through elements in an order, or
     * of a kind, the row does not write: which element stopped it is not something the row says,
     * so whether a reading's element was compared is left undecided — neither met nor missed.
     */
    @Test
    void overAContainerMadeOfTheInputWhichElementWasComparedIsNotSaid() {
        JsonNode reading = readingAt(MODEL, "List.any(x -> x > 0, List.reverse(xs))", "([1, 0])",
                "0");
        assertFalse(reading.path("hit").asBoolean(), () -> "not met: " + reading);
        assertEquals("partial", reading.path("status").asString(), () -> "and not missed either: "
                + reading);
        assertTrue(reading.path("weakening").toString().contains("border_observation_unavailable"),
                () -> "for want of what the run got to: " + reading);
    }

    /** Whether the reading at {@code against} of the guard's line was met by the one row. */
    private static boolean hitAt(String model, String guard, String row, String against) {
        return readingAt(model, guard, row, against).path("hit").asBoolean();
    }

    /** The reading at {@code against} of the guard's line, as the one row {@code row} met it. */
    private static JsonNode readingAt(String model, String guard, String row, String against) {
        Map<String, JsonNode> readings = new LinkedHashMap<>();
        JsonNode report = reportOfSource(model.replace("GUARD", guard) + """

                example pick
                    | "the row" : %s -> High
                """.formatted(row));
        collect(report, readings);
        JsonNode reading = readings.get(against);
        assertTrue(reading != null, () -> "a line has a point at " + against + ": " + readings);
        return reading;
    }

    private static void collect(JsonNode node, Map<String, JsonNode> out) {
        if (node.isObject() && node.has("against") && node.has("hit")) {
            JsonNode before = out.putIfAbsent(node.path("against").asString(), node);
            assertEquals(before == null ? node.path("hit") : before.path("hit"), node.path("hit"),
                    "one point, one answer");
        }
        node.forEach(child -> collect(child, out));
    }

    private static JsonNode reportOfSource(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }
}
