package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a line of a statement of several turns it is the same answer however many cases where it
 * decides there are, and so whether they were said one by one or as one.
 *
 * <p>Past a figure the cases are said as one condition, and a row on one side of the line and a
 * row on the other may each stand in a case of its own under it, which the line never turns
 * between. Asked of the condition, such a line was kept and owed rows no row could meet; asked of
 * each case, it is the line it is with the cases said one by one.
 */
class WhetherALineTurnsTheStatementDoesNotDependOnHowManyCasesItHasTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * A helper taking what it can of a cap, called on what the call before it left. Inside the
     * last call, the first call's choice of what is left is a part of the statement, and both of
     * its arms leave nought where its line is: the line turns nothing there. At three calls the
     * cases of that part are said one by one, at four they are past the figure and said as one,
     * and at five the last call's statement has more parts than a table of every way they come
     * out would hold; each way the line between {@code used} and the first cap is a border at the
     * first call alone.
     */
    @ParameterizedTest
    @ValueSource(ints = {3, 4, 5})
    void aLineNoCaseOfItTurnsIsOwedNothingWhereverItsCasesAreSaidAsOne(int calls) {
        JsonNode report = reportOf(takes(calls));
        List<JsonNode> against = bordersOn(report, "draw/used").stream()
                .filter(each -> each.path("value").asString().equals("held.h0"))
                .toList();
        assertEquals(1, against.size(),
                () -> "the first call's own line and no other, at " + calls + " calls: "
                        + against);
    }

    /**
     * What a reader is told of the four calls, with a row written: every point of the helper's
     * line is one a row is shown to be at or not, and none is held open by how many values a point
     * is tried with. Kept as a border, the line in the fourth call was owed rows no search could
     * find, each point undecided at that figure, though the figure decided nothing.
     */
    @Test
    void noPointOfTheLineIsHeldOpenByAFigureWhereNoRowCouldBeFound() {
        AdequacyReport report = measured(takes(4) + """

                example draw
                    | (MB(0), Held { h0 = MB(0), h1 = MB(1), h2 = MB(0), h3 = MB(0) }) -> MB(0)
                """);
        String human = report.human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        String border = human.lines()
                .dropWhile(line -> !line.strip().startsWith("border"))
                .takeWhile(line -> line.strip().startsWith("border") || line.startsWith("      "))
                .reduce("", (all, line) -> all + line + "\n");

        assertTrue(border.contains("obligations 1/4"), () -> "the border measure:\n" + human);
        assertFalse(border.contains("? undecided"),
                () -> "every point is one a row is at or is not:\n" + border);
        assertTrue(report.whatKeepsTheVerdictOpen().stream().noneMatch(open -> open.figures()
                        .contains(CompositionBudget.VALUES_A_POINT_IS_TRIED_WITH.figure())),
                () -> "and nothing is held open by how many values a point is tried with:\n"
                        + human);
    }

    /**
     * And a line that turns the statement in some of its cases is kept, said one by one or as
     * one: {@code x} compared with nought where an even number of truths hold, and nought
     * compared with it where they do not, is one statement whose line on {@code x} decides wherever
     * an even number of them hold — sixteen cases of five truths and thirty-two of six.
     */
    @Test
    void aLineSomeCaseOfItTurnsIsKeptWhereverItsCasesAreSaidAsOne() {
        for (int truths = 5; truths <= 6; truths++) {
            JsonNode report = reportOf(even(truths));
            int of = truths;
            assertFalse(bordersOn(report, "e/x").isEmpty(),
                    () -> "the line on x is a border, of " + of + " truths: " + report);
            assertFalse(reasonsAt(report, "x").contains("rule_never_turns_on_this_line"),
                    () -> "and not one the statement never turns on: " + reasonsAt(report, "x"));
        }
    }

    /**
     * What is asked one case at a time is where the statement turns, and not the rows reaching the
     * line: those are one set however many ways they come by. {@code Int.min(x, y) <= 5} turns on
     * the line through {@code x} where {@code y} is above five, and the rows come to it either
     * below nought or above ten — one side of the line along each way, and both sides together,
     * and a row on each differs from the other in the line alone.
     */
    @Test
    void rowsReachingALineAlongTwoWaysAreAskedTogether() {
        JsonNode report = reportOf("""
                module probe
                behavior g : (x: Int, y: Int) -> Int
                let g (x, y) = if x < 0 || x > 10 then (if Int.min(x, y) <= 5 then 1 else 2) else 3
                """);
        assertFalse(reasonsAt(report, "x").contains("rule_never_turns_on_this_line"),
                () -> "the statement turns between a row below nought and one above ten: "
                        + reasonsAt(report, "x"));
        assertFalse(bordersOn(report, "g/x").isEmpty(),
                () -> "the line through x is a border: " + report);
    }

    /** A helper called {@code calls} times, each on what the last left. */
    private static String takes(int calls) {
        StringBuilder held = new StringBuilder();
        StringBuilder body = new StringBuilder();
        String before = "used";
        for (int i = 0; i < calls; i++) {
            held.append(i == 0 ? "" : ", ").append("h").append(i).append(": MB");
            body.append("    let (a").append(i).append(", rest").append(i).append(") = take(")
                    .append(before).append(", held.h").append(i).append(")\n");
            before = "rest" + i;
        }
        return """
                module probe.drawing

                data MB = Int
                    invariant value >= 0
                data Held = { HELD }

                behavior draw : (used: MB, held: Held) -> MB

                let draw (used, held) = {
                BODY    LAST
                }

                let take (used: MB, cap: MB): (MB, MB) =
                    if used.value <= cap.value then (used, MB(0)) else (cap, MB(used.value - cap.value))
                """.replace("HELD", held).replace("BODY", body).replace("LAST", before);
    }

    /** A comparison of {@code x} where an even number of {@code truths} truths hold, and of
     *  nought where they do not. */
    private static String even(int truths) {
        List<String> ways = new ArrayList<>();
        for (int each = 0; each < 1 << truths; each++) {
            if (Integer.bitCount(each) % 2 != 0) {
                continue;
            }
            List<String> parts = new ArrayList<>();
            for (int i = 0; i < truths; i++) {
                parts.add((each >> i & 1) == 1 ? "t" + i : "Bool.not(t" + i + ")");
            }
            ways.add("(" + String.join(" && ", parts) + ")");
        }
        List<String> names = new ArrayList<>();
        List<String> typed = new ArrayList<>();
        for (int i = 0; i < truths; i++) {
            names.add("t" + i);
            typed.add("t" + i + ": Bool");
        }
        return """
                module probe
                behavior e : (x: Int, TYPED) -> Int
                let e (x, NAMES) = if (if EVEN then x else 0) > 0 then 1 else 0
                """.replace("TYPED", String.join(", ", typed))
                .replace("NAMES", String.join(", ", names))
                .replace("EVEN", String.join(" || ", ways));
    }

    private static JsonNode reportOf(String source) {
        return JSON.readTree(measured(source)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    private static AdequacyReport measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "compiles: " + compilation.errors());
        return AdequacyReport.of(compilation);
    }

    /** Every border on {@code axis}. */
    private static List<JsonNode> bordersOn(JsonNode report, String axis) {
        List<JsonNode> out = new ArrayList<>();
        borders(report, axis, out);
        return out;
    }

    private static void borders(JsonNode node, String axis, List<JsonNode> out) {
        if (node.isObject() && node.has("items") && node.has("lineId")
                && axis.equals(node.path("axis").asString())) {
            out.add(node);
        }
        node.forEach(child -> borders(child, axis, out));
    }

    /** Every reason a rule was said to leave {@code position} with. */
    private static List<String> reasonsAt(JsonNode report, String position) {
        List<String> out = new ArrayList<>();
        reasons(report, position, out);
        return out;
    }

    private static void reasons(JsonNode node, String position, List<String> out) {
        if (node.isObject() && node.has("ruleId") && node.has("reason")
                && position.equals(node.path("position").asString())) {
            out.add(node.path("reason").asString());
        }
        node.forEach(child -> reasons(child, position, out));
    }
}
