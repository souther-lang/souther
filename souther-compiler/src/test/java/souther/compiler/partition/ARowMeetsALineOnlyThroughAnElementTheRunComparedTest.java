package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.Collections;
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

    /**
     * A closure handed values written out is applied to each, and on one of them may take an arm
     * the comparison is not in: the run got an answer out of the comparison on the other value,
     * and nothing compared this one.
     */
    @Test
    void anApplicationThatTakesAnotherArmComparesNothing() {
        String model = """
                module probe

                data Low
                data High
                data K1
                data K2
                data Kind = K1 | K2
                data Item = { kind: Kind, v: Int }

                behavior pick : (a: Item, b: Item) -> Low | High
                let pick (a, b) =
                    if List.all(x -> match x.kind with | K1 -> x.v > 5 | K2 -> true, [a, b])
                    then High else Low
                """;
        assertFalse(hitOn(model, "(Item { kind = K1, v = 7 }, Item { kind = K2, v = 6 })",
                        "pick/b.v", "6"),
                "b takes the other arm: the comparison was made on a, and never on b");
        assertTrue(hitOn(model, "(Item { kind = K1, v = 7 }, Item { kind = K1, v = 6 })",
                        "pick/b.v", "6"),
                "b takes the arm, so the comparison is made on it");
    }

    /**
     * Inside a closure whose applications are not said — handed more values than are read — which
     * elements the comparison is made on is not said either, and that includes what the closure
     * around it already knew: {@code List.any} stops at the first element, and the inner closure is
     * made on it, but whether it is made on the second is what is not said. The second element's
     * point is left undecided rather than met for want of knowing.
     */
    @Test
    void insideAClosureWhoseApplicationsAreNotSaidNoElementIsMetForWantOfKnowing() {
        String many = String.join(", ", Collections.nCopies(257, "n"));
        String model = """
                module probe

                data Low
                data High

                behavior pick : (xs: List<Int>, n: Int) -> Low | High
                let pick (xs, n) = if GUARD then High else Low
                """;
        JsonNode reading = readingAt(model, "List.any(x -> List.any(y -> x > 0, [" + many
                + "]), xs)", "([1, 0], 0)", "0");
        assertFalse(reading.path("hit").asBoolean(),
                () -> "the walk stops at the first element: " + reading);
        assertEquals("partial", reading.path("status").asString(),
                () -> "and which elements the inner closure is made on is not said: " + reading);
    }

    /**
     * And what is not said is said of the elements it is not known of. A comparison inside such a
     * closure that reads no element of any container is about none of them: a run recorded through
     * it is a run that compared what the row stands at there, whichever applications were made.
     */
    @Test
    void aComparisonAboutNoElementIsMetWhereverARunMadeIt() {
        String many = String.join(", ", Collections.nCopies(257, "n"));
        String model = """
                module probe

                data Low
                data High

                behavior pick : (xs: List<Int>, n: Int) -> Low | High
                let pick (xs, n) = if GUARD then High else Low
                """;
        assertTrue(hitAt(model, "List.any(y -> n > 0, [" + many + "])", "([1], 0)", "0"),
                "n is compared on the first application, and the row stands at 0");
    }

    /**
     * An operation applying its closure to one value it picks out — the value under a key — makes
     * the comparison on that one: a run getting an answer out of it says nothing of the values it
     * did not pick.
     */
    @Test
    void anOperationApplyingItsClosureToOneValueSaysNothingOfTheOthers() {
        String model = """
                module probe

                data Low
                data High

                behavior pick : (k: String, m: Map<String, Int>) -> Low | High
                let pick (k, m) = if GUARD then High else Low
                """;
        JsonNode reading = readingAt(model, "Map.size(Map.filterEntries((_, w) -> w == 1,"
                + " Map.updateIfPresent(k, v -> if v > 0 then 1 else 2, m))) >= 1",
                "(\"a\", [(\"a\", 1), (\"b\", 0)])", "0");
        assertFalse(reading.path("hit").asBoolean(),
                () -> "the closure is applied under a, and b's value is never compared: "
                        + reading);
    }

    /** Whether the reading at {@code against} on {@code axis} was met by the one row, for a model
     *  whose guard is written in. */
    private static boolean hitOn(String model, String row, String axis, String against) {
        JsonNode report = reportOfSource(model + """

                example pick
                    | "the row" : %s -> High
                """.formatted(row));
        JsonNode[] found = {null};
        readingOn(report, axis, against, found);
        assertTrue(found[0] != null, () -> "a line on " + axis + " has a point at " + against
                + ": " + report);
        return found[0].path("hit").asBoolean();
    }

    private static void readingOn(JsonNode node, String axis, String against, JsonNode[] found) {
        if (node.isObject() && axis.equals(node.path("axis").asString())
                && against.equals(node.path("against").asString()) && node.has("hit")) {
            found[0] = node;
        }
        node.forEach(child -> readingOn(child, axis, against, found));
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
