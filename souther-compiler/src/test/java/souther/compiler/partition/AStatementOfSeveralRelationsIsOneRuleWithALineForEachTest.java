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
 * A comparison stating several relations held together is one rule, with a line for each relation,
 * owed rows only where the statement turns on that line.
 *
 * <p>{@code Int.max(a, b) > 5} is {@code a > 5} or {@code b > 5}. It is one rule an author wrote,
 * and it draws a line on {@code a} and a line on {@code b} — two lines of one rule, each named by
 * the reading that found it. The line on {@code a} decides the outcome only where {@code b} is not
 * already above five, so a row standing at it with {@code b} above five is answered the same way on
 * both sides of it and does not meet it. And a line the statement turns on nowhere a row reaches is
 * said to be one, rather than owed rows that could never tell anything apart.
 */
class AStatementOfSeveralRelationsIsOneRuleWithALineForEachTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module probe

            data Low
            data High
            data Pos = { v: Int }
                invariant v >= 1

            behavior pick : (a: Int, b: Pos) -> Low | High
            let pick (a, b) = if GUARD then High else Low
            """;

    @Test
    void eachRelationIsALineOfTheOneRule() {
        JsonNode report = reportOf("Int.max(a, b.v) > 5", "");
        Set<Integer> parts = new TreeSet<>();
        Set<String> rules = new TreeSet<>();
        for (JsonNode obligation : obligationsOfParts(report)) {
            parts.add(obligation.at("/obligationId/line/which/part").asInt());
            rules.add(obligation.at("/obligationId/line/which/rule").toString());
        }
        assertEquals(1, rules.size(), () -> "one comparison, one rule: " + rules);
        // And not the line between the two arms of max, which the reading also holds: where a
        // crosses b.v the answer does not jump, so no row on either side of it is in a case where
        // the statement turns.
        assertEquals(Set.of(0, 1), parts, "the line on a and the line on b");
        assertTrue(reasonsAt(report, "a").stream()
                        .noneMatch("several_lines_in_one_rule"::equals),
                "the statement is drawn, not held back");
    }

    @Test
    void aLineTheStatementNeverTurnsOnIsSaidToBeOne() {
        // Wherever a reaches five, a + b.v is already above five, since b.v is at least one: the
        // line on a decides nothing any row reaches, and the line on the sum decides everything.
        JsonNode report = reportOf("Int.max(a, a + b.v) > 5", "");
        assertTrue(reasonsAt(report, "a").contains("rule_never_turns_on_this_line"),
                () -> "the line on a decides nowhere: " + reasonsAt(report, "a"));
        assertTrue(obligationsOfParts(report).stream()
                        .noneMatch(each -> each.path("readings").get(0).path("axis").asString()
                                .equals("pick/a")),
                "and no row is owed at it");
    }

    /**
     * Where the two arms of an operation meet and its answer does not jump, the line between them
     * decides nothing: {@code Int.max(0, a) <= b.v} states {@code a >= 0} once held and once
     * denied, and on the line either arm gives nought. It decides where one arm is within
     * {@code b.v} and the other is not, which is two cases — and on the line both arms are nought,
     * so neither case has a row there.
     */
    @Test
    void theLineWhereTwoArmsMeetDecidesNothing() {
        JsonNode report = reportOf("Int.max(0, a) <= b.v", "");
        assertTrue(reasonsAt(report, "a").contains("rule_never_turns_on_this_line"),
                () -> "the line between the arms decides nowhere: " + reasonsAt(report, "a"));
    }

    /**
     * A line turns the statement only where rows on both sides of it are in one case of where it
     * decides, and not where the case holds on one side alone.
     *
     * <p>{@code Int.min(a, 11 - a) > 5} is {@code a > 5} and {@code 11 - a > 5}, and it holds of no
     * whole number. Read part against part, the line on {@code 11 - a > 5} decides where
     * {@code a > 5} — and six is above five — but a row crossing that line goes from six to five,
     * taking {@code a > 5} across with it, and the statement is false on both sides. So neither
     * line is one the statement turns on, and neither is owed a row.
     */
    @Test
    void aLineTurnsTheStatementOnlyWhereBothItsSidesAreInOneCase() {
        JsonNode report = reportOf("Int.min(a, 11 - a) > 5", "");
        assertEquals(List.of("rule_never_turns_on_this_line"),
                reasonsAt(report, "a").stream().distinct().toList(),
                () -> "neither line turns the statement: " + reasonsAt(report, "a"));
        assertTrue(obligationsOfParts(report).isEmpty(),
                () -> "and no row is owed at either: " + obligationsOfParts(report));
    }

    /**
     * A relation that names a value is crossed between that value and one beside it, and is a line
     * of the statement where a row can stand at both in one case.
     *
     * <p>{@code Int.max(a, b.v) == 6} names six of whichever is larger: with {@code b.v} below six,
     * {@code a} at six and {@code a} at five are answered differently, and so is {@code b.v} with
     * {@code a} below six.
     */
    @Test
    void aRelationNamingAValueIsALineWhereItsValueAndOneBesideItAreInOneCase() {
        Set<String> axes = new TreeSet<>();
        for (JsonNode obligation : obligationsOfParts(reportOf("Int.max(a, b.v) == 6", ""))) {
            JsonNode reading = obligation.path("readings").get(0);
            if (reading.path("against").asString().equals("6")) {
                axes.add(reading.path("axis").asString());
            }
        }
        assertEquals(Set.of("pick/a", "pick/b.v"), axes,
                "a line at six on each of the two, where the other is below it");
    }

    /**
     * A clause has nowhere to hold where each of its lines decides — no way leads to it for a
     * condition to be carried on — so it draws none of them and says why, rather than drawing them
     * and owing rows the clause answers alike on both sides.
     */
    @Test
    void aClauseOfSeveralRelationsDrawsNoneOfThem() {
        Compilation compilation = Compilation.ofSource("""
                module probe

                data Low
                data High

                behavior pick : (a: Int, b: Int) -> Low | High
                    ensures big = High -> Int.max(a, b) > 5
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "compiles: " + compilation.errors());
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        assertTrue(obligationsOfParts(report).isEmpty(), "no line of the clause is drawn");
        assertTrue(reasonsAt(report, "a").contains("several_lines_in_one_rule"),
                () -> "and the clause says so: " + reasonsAt(report, "a"));
    }

    @Test
    void aRowAtTheLineMeetsItOnlyWhereTheStatementTurnsOnIt() {
        // Both rows stand at a = 6, the line on a's point above five. In the first b.v is nine and
        // the statement holds on both sides of the line; in the second it is two, and the line is
        // what decides.
        assertFalse(theLineOnAIsMetAtSixBy("""
                example pick
                    | "settled by b" : (6, Pos { v = 9 }) -> High
                """), "b already above five answers the statement on both sides of the line");
        assertTrue(theLineOnAIsMetAtSixBy("""
                example pick
                    | "decided by a" : (6, Pos { v = 2 }) -> High
                """), "b below five leaves the statement to the line");
    }

    /** Whether the point at a = 6 of the line on a was met by the rows {@code examples} writes. */
    private static boolean theLineOnAIsMetAtSixBy(String examples) {
        JsonNode report = reportOf("Int.max(a, b.v) > 5", examples);
        for (JsonNode obligation : obligationsOfParts(report)) {
            JsonNode reading = obligation.path("readings").get(0);
            if (reading.path("axis").asString().equals("pick/a")
                    && reading.path("against").asString().equals("6")) {
                return reading.path("hit").asBoolean();
            }
        }
        throw new AssertionError("the line on a has a point at six: " + report);
    }

    private static JsonNode reportOf(String guard, String examples) {
        Compilation compilation = Compilation.ofSource(
                MODEL.replace("GUARD", guard) + "\n" + examples, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "compiles: " + compilation.errors());
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    /** Every obligation owed at a line of a statement of several. */
    private static List<JsonNode> obligationsOfParts(JsonNode report) {
        List<JsonNode> out = new ArrayList<>();
        collect(report, out);
        return out;
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("point") && node.has("readings")
                && "part_of_comparison".equals(
                        node.at("/obligationId/line/which/kind").asString())) {
            out.add(node);
        }
        node.forEach(child -> collect(child, out));
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
