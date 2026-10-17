package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Filtered counts added up and held against a number that comes to whether any of them is above
 * nought are the checks they come to: the lines are the closures' on each element, the same lines
 * the checks written one by one draw, and the comparison draws none of its own beside them.
 *
 * <p>A sum held past that says how many, and is still the comparison's own rule; so is a sum of
 * sizes of the input, which nothing inside the comparison states.
 */
class CountsAddedUpAgainstNoughtDrawTheLinesOfTheChecksTheyComeToTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String X = "List.length(List.filter(x -> x > 0, xs))";

    private static final String Y = "List.length(List.filter(y -> y > 0, ys))";

    @Test
    void aSumAgainstOneIsTheChecksJoinedByOr() {
        assertSameLines(X + " >= 1 || " + Y + " >= 1", X + " + " + Y + " >= 1");
        assertSameLines(X + " >= 1 || " + Y + " >= 1", "2 * " + X + " + 3 * " + Y + " >= 2");
    }

    @Test
    void aSumAgainstNoughtIsTheChecksDeniedJoinedByAnd() {
        assertSameLines(X + " == 0 && " + Y + " == 0", X + " + " + Y + " == 0");
    }

    @Test
    void oneCountWrittenLongerIsTheCheckItIs() {
        assertSameLines(X + " >= 1", X + " + 0 >= 1");
        assertSameLines(X + " >= 1", "2 * " + X + " >= 2");
    }

    /** Holding on every row, the sum is a rule of the comparison's that cuts nothing, as one count
     *  at or above nought is. */
    @Test
    void aSumAtOrAboveNoughtIsTheComparisonsRuleAsOneCountIs() {
        for (String condition : List.of(X + " >= 0", X + " + " + Y + " >= 0")) {
            JsonNode report = reportOf(condition);
            assertEquals(Set.of("comparison"), Set.copyOf(notReadAt(report)), condition);
            assertEquals(Set.of("rule_cuts_nothing"), Set.copyOf(whyNotRead(report)), condition);
        }
    }

    /** Read as the check only once the numbers of the input are taken away, the comparison is
     *  read as the check where it is read itself. */
    @Test
    void aCountThatComesToTheCheckOnceReadIsReadAsIt() {
        assertTrue(notReadAt(reportOf(X + " + n - n >= 1")).isEmpty());
    }

    /** The rows composed for the sum take the guard both ways. */
    @Test
    void theRowsComposedTakeTheGuardBothWays() {
        Set<Boolean> held = new LinkedHashSet<>();
        Matcher row = Pattern.compile("\\(\\[([^\\]]*)\\], \\[([^\\]]*)\\], -?\\d+\\)")
                .matcher(rowsOf(X + " + " + Y + " >= 1"));
        while (row.find()) {
            held.add(positives(row.group(1)) + positives(row.group(2)) >= 1);
        }
        assertEquals(Set.of(true, false), held);
    }

    @Test
    void aSumThatSaysHowManyIsTheComparisonsOwnRule() {
        for (String condition : List.of(X + " + " + Y + " >= 2", X + " - " + Y + " >= 1")) {
            List<String> filedAt = notReadAt(reportOf(condition));
            assertFalse(filedAt.isEmpty(), () -> condition + " is not read");
            assertEquals(Set.of("comparison"), Set.copyOf(filedAt),
                    () -> condition + " is the comparison's: " + filedAt);
        }
    }

    @Test
    void aSumOfSizesOfTheInputIsALineOnTheSum() {
        JsonNode report = reportOf("List.length(xs) + List.length(ys) >= 1");
        List<JsonNode> lines = boundaries(report);
        assertEquals(1, lines.size(), () -> "one line: " + lines);
        assertEquals(2, lines.getFirst().path("lineId").path("target").path("quantity")
                .path("terms").size(), () -> "on the sum: " + lines);
        assertEquals(Set.of("comparison"), Set.copyOf(notReadAt(report)));
    }

    /** The lines both draw, the same apart from which comparison of each is which. */
    private static void assertSameLines(String written, String added) {
        JsonNode one = reportOf(written);
        JsonNode other = reportOf(added);
        assertTrue(notReadAt(other).isEmpty(), () -> added + " is read: " + other);
        List<JsonNode> expected = boundaries(one);
        assertFalse(expected.isEmpty(), () -> written + " draws lines");
        assertEquals(expected, boundaries(other), () -> added + " draws what " + written + " does");
    }

    private static List<JsonNode> boundaries(JsonNode report) {
        List<JsonNode> out = new ArrayList<>();
        collect(report, "boundaries", out);
        out.forEach(CountsAddedUpAgainstNoughtDrawTheLinesOfTheChecksTheyComeToTest::unnumbered);
        return out;
    }

    /** What kind of construct each rule no line was read off is. */
    private static List<String> notReadAt(JsonNode report) {
        return ofWhatWasNotRead(report, "ruleId", "kind");
    }

    private static List<String> whyNotRead(JsonNode report) {
        return ofWhatWasNotRead(report, "reason");
    }

    private static List<String> ofWhatWasNotRead(JsonNode report, String... path) {
        List<JsonNode> entries = new ArrayList<>();
        collect(report, "notRead", entries);
        List<String> out = new ArrayList<>();
        for (JsonNode each : entries) {
            JsonNode at = each;
            for (String field : path) {
                at = at.path(field);
            }
            out.add(at.asString());
        }
        return out;
    }

    private static void collect(JsonNode node, String field, List<JsonNode> out) {
        if (node.isObject() && node.has(field)) {
            node.get(field).forEach(out::add);
        }
        node.forEach(child -> collect(child, field, out));
    }

    /** Leaves out the numbers the comparisons are told apart by, which count every construct. */
    private static void unnumbered(JsonNode node) {
        if (node instanceof ObjectNode object) {
            object.remove("ordinal");
        }
        node.forEach(CountsAddedUpAgainstNoughtDrawTheLinesOfTheChecksTheyComeToTest::unnumbered);
    }

    private static long positives(String elements) {
        return Pattern.compile("-?\\d+").matcher(elements).results()
                .filter(each -> Integer.parseInt(each.group()) > 0).count();
    }

    private static String source(String condition) {
        return """
                module probe
                data No
                behavior some : (xs: List<Int>, ys: List<Int>, n: Int) -> Bool | No
                let some (xs, ys, n) = {
                    guard %s else No
                    true
                }
                """.formatted(condition);
    }

    private static JsonNode reportOf(String condition) {
        Compilation compilation = compiled(condition);
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    private static String rowsOf(String condition) {
        return GeneratedRows.of(compiled(condition), "probe", null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
    }

    private static Compilation compiled(String condition) {
        Compilation compilation = Compilation.ofSource(source(condition), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
