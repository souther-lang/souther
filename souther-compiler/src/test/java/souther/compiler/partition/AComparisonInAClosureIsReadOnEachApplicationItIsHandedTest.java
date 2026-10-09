package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison inside a closure handed the values a container was written with is read on each
 * application, and a line it draws on one application is owed rows only where a run makes that
 * application.
 *
 * <p>{@code List.any(x -> x > 5, [a, b])} is one rule an author wrote, and it draws a line on
 * {@code a} and a line on {@code b}. {@code List.any} answers once one element holds, so the
 * closure is applied to {@code b} only where it answered false of {@code a}: a row at the line on
 * {@code b} with {@code a} above five never meets it. {@code List.all} stops the other way round,
 * and an operation that stops nowhere applies the closure to every value whatever the others
 * answer.
 */
class AComparisonInAClosureIsReadOnEachApplicationItIsHandedTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module probe

            data Low
            data High

            behavior pick : (a: Int, b: Int) -> Low | High
            let pick (a, b) = if GUARD then High else Low
            """;

    @Test
    void eachApplicationDrawsALineOfTheOneRule() {
        JsonNode report = reportOf("List.any(x -> x > 5, [a, b])", "");
        Set<String> rules = new TreeSet<>();
        Set<Integer> parts = new TreeSet<>();
        for (JsonNode obligation : obligationsOfParts(report)) {
            rules.add(obligation.at("/obligationId/line/which/rule").toString());
            parts.add(obligation.at("/obligationId/line/which/part").asInt());
        }
        assertEquals(1, rules.size(), () -> "one comparison, one rule: " + rules);
        assertEquals(Set.of(0, 1), parts, "a line on a and a line on b");
        assertEquals(Set.of("pick/a", "pick/b"), axesOfParts(report));
    }

    @Test
    void anOperationThatStopsAtAHoldingAnswerReachesTheNextOnlyPastAFailingOne() {
        String guard = "List.any(x -> x > 5, [a, b])";
        assertTrue(metAt(guard, "(0, 6)", "pick/b", "6"),
                "a at nought answers false, so the closure is applied to b");
        assertFalse(metAt(guard, "(9, 6)", "pick/b", "6"),
                "a above five answers true, and nothing is applied to b");
    }

    @Test
    void anOperationThatStopsAtAFailingAnswerReachesTheNextOnlyPastAHoldingOne() {
        String guard = "List.all(x -> x > 5, [a, b])";
        assertTrue(metAt(guard, "(9, 6)", "pick/b", "6"),
                "a above five answers true, so the closure is applied to b");
        assertFalse(metAt(guard, "(0, 6)", "pick/b", "6"),
                "a at nought answers false, and nothing is applied to b");
    }

    @Test
    void anOperationThatStopsNowhereAppliesTheClosureToEveryValue() {
        String guard = "List.length(List.filter(x -> x > 5, [a, b])) >= 1";
        assertTrue(metAt(guard, "(9, 6)", "pick/b", "6"), "whatever a answered");
        assertTrue(metAt(guard, "(0, 6)", "pick/b", "6"), "whatever a answered");
    }

    /**
     * Two applications stating one thing are one line, reached wherever either is made — and the
     * first is made on every run, so the line is one a comparison outside every closure would be.
     */
    @Test
    void twoApplicationsStatingOneLineAreOneLine() {
        JsonNode report = reportOf("List.any(x -> x > 5, [a, a])", "");
        assertTrue(obligationsOfParts(report).isEmpty(),
                () -> "one line, not one per application: " + obligationsOfParts(report));
        assertTrue(axesOf(report, "comparison").contains("pick/a"),
                () -> "drawn on a: " + axesOf(report, "comparison"));
    }

    /**
     * What the closure answered on the applications before one is the whole of its answer, and
     * not the comparison alone: {@code a} at nought leaves the guard failing and the answer false,
     * so the closure goes on to {@code b}, and {@code a} at two answers true and stops it.
     */
    @Test
    void whatStopsTheWalkIsWhatTheClosureAnswered() {
        String guard = "List.any(x -> if x > 0 then x < 5 else false, [a, b])";
        assertTrue(metAt(guard, "(0, 4)", "pick/b", "4"), "a at nought answers false");
        assertFalse(metAt(guard, "(2, 4)", "pick/b", "4"), "a at two answers true");
    }

    /**
     * What holds on the way to a comparison inside the closure is said of each application.
     *
     * <p>{@code x < 5} under {@code x > b} is met at four on {@code a} only where four is above
     * {@code b}. Read with the parameter standing for any of the values at once, the guard would be
     * read of no value at all, and the line would be owed rows the comparison is never taken on.
     */
    @Test
    void whatHoldsOnTheWayInsideTheClosureIsSaidOfEachApplication() {
        String guard = "List.any(x -> if x > b then x < 5 else false, [a])";
        assertTrue(metAt(guard, "(4, 0)", "pick/a", "4"), "four is above nought");
        assertFalse(metAt(guard, "(4, 9)", "pick/a", "4"), "four is not above nine");
    }

    /**
     * Where an application is made is said in what a row's numbers answer, or no line is drawn.
     *
     * <p>{@code List.any(x -> x > 5 || flag, [a, b])} applies the closure to {@code b} only where
     * {@code flag} is false, and a truth is no number of a row: a row at the line on {@code b}
     * could not be asked whether the closure got to {@code b}. So the comparison is held back with
     * its reason, and not drawn as though the second application were made on every run.
     */
    @Test
    void whereAnApplicationIsMadeSaidOfNoNumberDrawsNoLine() {
        JsonNode report = reportOfSource("""
                module probe

                data Low
                data High

                behavior pick : (a: Int, b: Int, flag: Bool) -> Low | High
                let pick (a, b, flag) = if List.any(x -> x > 5 || flag, [a, b]) then High else Low
                """);
        assertTrue(obligationsOfParts(report).isEmpty(),
                () -> "no line is drawn: " + obligationsOfParts(report));
        assertTrue(reasonsAt(report, "b", "comparison").contains("several_lines_in_one_rule"),
                () -> "and the comparison says why: " + reasonsAt(report, "b", "comparison"));
    }

    /**
     * A closure applied more times than a condition is read on is read once, as it stands, and a
     * comparison in it that stops is filed at every position the values it was handed name — and
     * not at none of them, which would be a rule no measure reads and no report mentions.
     */
    @Test
    void aClosureAppliedMoreTimesThanAreReadIsFiledAtEveryValueItWasHanded() {
        StringBuilder values = new StringBuilder("a");
        for (int i = 1; i <= 16; i++) {
            values.append(", ").append(i);
        }
        JsonNode report = reportOf("List.any(x -> List.any(y -> x > y + b, [" + values
                + "]), [" + values + "])", "");
        assertFalse(reasonsAt(report, "a", "comparison").isEmpty(),
                () -> "filed at a, which x stands for: " + reasonsAt(report, "a", "comparison"));
        assertFalse(reasonsAt(report, "b", "comparison").isEmpty(), "and at b");
    }

    /** Whether the reading at {@code against} on {@code axis} of the comparison's lines was met by
     *  the row {@code row}. */
    private static boolean metAt(String guard, String row, String axis, String against) {
        JsonNode report = reportOf(guard, """
                example pick
                    | "the row" : %s -> High
                """.formatted(row));
        for (JsonNode obligation : obligationsOfParts(report)) {
            JsonNode reading = obligation.path("readings").get(0);
            if (reading.path("axis").asString().equals(axis)
                    && reading.path("against").asString().equals(against)) {
                return reading.path("hit").asBoolean();
            }
        }
        throw new AssertionError("a line on " + axis + " has a point at " + against + ": "
                + report);
    }

    private static JsonNode reportOf(String guard, String examples) {
        return reportOfSource(MODEL.replace("GUARD", guard) + "\n" + examples);
    }

    private static JsonNode reportOfSource(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        // An example whose answer is not the model's is still a row the model is run on, which is
        // all that is asked of it here.
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    private static Set<String> axesOfParts(JsonNode report) {
        return axesOf(report, "part_of_comparison");
    }

    /** Every axis an obligation at a line of the kind {@code kind} is read on. */
    private static Set<String> axesOf(JsonNode report, String kind) {
        List<JsonNode> obligations = new ArrayList<>();
        collect(report, kind, obligations);
        Set<String> axes = new TreeSet<>();
        for (JsonNode obligation : obligations) {
            axes.add(obligation.path("readings").get(0).path("axis").asString());
        }
        return axes;
    }

    /** Every obligation owed at a line of one comparison's several. */
    private static List<JsonNode> obligationsOfParts(JsonNode report) {
        List<JsonNode> out = new ArrayList<>();
        collect(report, "part_of_comparison", out);
        return out;
    }

    private static void collect(JsonNode node, String kind, List<JsonNode> out) {
        if (node.isObject() && node.has("point") && node.has("readings")
                && kind.equals(node.at("/obligationId/line/which/kind").asString())) {
            out.add(node);
        }
        node.forEach(child -> collect(child, kind, out));
    }

    /** Every reason a rule of the kind {@code kind} was said to leave {@code position} with. */
    private static List<String> reasonsAt(JsonNode report, String position, String kind) {
        List<String> out = new ArrayList<>();
        reasons(report, position, kind, out);
        return out;
    }

    private static void reasons(JsonNode node, String position, String kind, List<String> out) {
        if (node.isObject() && node.has("ruleId") && node.has("reason")
                && position.equals(node.path("position").asString())
                && kind.equals(node.at("/ruleId/kind").asString())) {
            out.add(node.path("reason").asString());
        }
        node.forEach(child -> reasons(child, position, kind, out));
    }
}
