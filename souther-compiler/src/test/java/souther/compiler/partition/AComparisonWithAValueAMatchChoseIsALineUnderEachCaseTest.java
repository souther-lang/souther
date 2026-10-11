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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison against a value a match chose by the case of a position is a line for each arm,
 * deciding where the position is in that arm's case.
 *
 * <p>{@code days <= limit(s)}, with {@code limit} choosing two, seven or fourteen by the stage, is
 * {@code days <= 2} where {@code s} is {@code Hot}, {@code days <= 7} where it is {@code Warm} and
 * {@code days <= 14} where it is {@code Cold}. A row says which stage it wrote, so each line is
 * owed rows of its own case and is met by no row of another. The same holds where the case is
 * asked through a helper answering a truth, {@code if isDis(d) then 1800 else 1300}.
 */
class AComparisonWithAValueAMatchChoseIsALineUnderEachCaseTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String STAGES = """
            module probe

            data Stage = Hot | Warm | Cold
            data Late = { n: Int }
            data Ok = { k: Int }

            let limit (s: Stage): Int =
                match s with
                    | Hot -> 2
                    | Warm -> 7
                    | Cold -> 14

            behavior chk : (s: Stage, days: Int) -> Ok | Late
                constructs Ok, Late
            let chk (s, days) = {
                guard days <= limit(s) else Late { n = 0 }
                Ok { k = 1 }
            }
            """;

    private static final String DISABILITY = """
            module probe

            data Dis = Healthy | Disabled

            let isDis (d: Dis): Bool = match d with
                Healthy -> false
              | Disabled -> true

            behavior f : (rev: Int, d: Dis) -> Int
            let f (rev, d) = if rev >= (if isDis(d) then 1800 else 1300) then 1 else 2
            """;

    @Test
    void eachArmOfTheMatchIsALineOfTheOneRule() {
        JsonNode report = reportOf(STAGES, "");
        assertTrue(reasonsAt(report, "days").stream()
                        .noneMatch("several_lines_in_one_rule"::equals),
                () -> "the statement is drawn: " + reasonsAt(report, "days"));
        assertEquals(Set.of("2", "3", "7", "8", "14", "15"), pointsOn(report, "chk/days"),
                "a line at each limit the match chooses");
    }

    /**
     * A row of one stage meets the line of its own stage and no other: two days is on the line
     * for {@code Hot}, and a {@code Warm} row at two days is nowhere near the line for {@code Warm}.
     */
    @Test
    void aRowMeetsOnlyTheLineOfItsOwnCase() {
        assertEquals(Set.of("2", "3"), pointsMetOn(reportOf(STAGES, """
                example chk
                    | "hot on" : (Hot, 2) -> Ok { k = 1 }
                    | "hot past" : (Hot, 3) -> Late { n = 0 }
                """), "chk/days"), "a Hot row meets the line at two");
        assertEquals(Set.of(), pointsMetOn(reportOf(STAGES, """
                example chk
                    | "warm at two" : (Warm, 2) -> Ok { k = 1 }
                    | "warm at three" : (Warm, 3) -> Ok { k = 1 }
                """), "chk/days"), "and a Warm row at two or three meets no line");
        assertEquals(Set.of("7", "8"), pointsMetOn(reportOf(STAGES, """
                example chk
                    | "warm on" : (Warm, 7) -> Ok { k = 1 }
                    | "warm past" : (Warm, 8) -> Late { n = 0 }
                """), "chk/days"), "a Warm row meets the line at seven");
    }

    /**
     * The runs between the lines are the classes of {@code days}, which every line on it bounds
     * whatever case it decides in; a row in one is owed to a line only where it is in that line's
     * case. Five days at {@code Warm} is in the run above the line for {@code Hot} and below the
     * line for {@code Warm}, and is the second of those and not the first.
     */
    @Test
    void aRowInARunIsOwedOnlyToTheLineOfItsOwnCase() {
        JsonNode report = reportOf(STAGES, """
                example chk
                    | "warm five" : (Warm, 5) -> Ok { k = 1 }
                """);
        List<String> met = new ArrayList<>();
        regions(report, met);
        assertEquals(List.of("7 below 2 < days < 7"), met,
                "the run below the line for Warm, and not the same run above the line for Hot");
    }

    /** Each run a row of the examples is in, as the line it is owed to, the side and the run. */
    private static void regions(JsonNode node, List<String> out) {
        if (node.isObject() && node.has("point") && node.has("readings")
                && "in_the_region".equals(node.at("/obligationId/location/kind").asString())
                && node.path("readings").get(0).path("hit").asBoolean()) {
            out.add(node.at("/obligationId/level/at").asString() + " "
                    + node.at("/obligationId/location/side").asString() + " "
                    + node.path("readings").get(0).path("against").asString());
        }
        node.forEach(child -> regions(child, out));
    }

    @Test
    void aTruthAHelperReadsOffTheCaseChoosesTheLineTheSameWay() {
        JsonNode report = reportOf(DISABILITY, "");
        assertTrue(reasonsAt(report, "rev").stream()
                        .noneMatch("several_lines_in_one_rule"::equals),
                () -> "the statement is drawn: " + reasonsAt(report, "rev"));
        assertEquals(Set.of("1300", "1299", "1800", "1799"), pointsOn(report, "f/rev"),
                "a line at each ceiling");
        assertEquals(Set.of(), pointsMetOn(reportOf(DISABILITY, """
                example f
                    | "healthy at the higher" : (1800, Healthy) -> 1
                    | "healthy below it" : (1799, Healthy) -> 1
                """), "f/rev"), "a Healthy row meets no line at 1800");
        assertEquals(Set.of("1800", "1799"), pointsMetOn(reportOf(DISABILITY, """
                example f
                    | "disabled at it" : (1800, Disabled) -> 1
                    | "disabled below it" : (1799, Disabled) -> 2
                """), "f/rev"), "and a Disabled row does");
    }

    /** Every value at or beside a line of the statement a row is owed at, on {@code axis}. */
    private static Set<String> pointsOn(JsonNode report, String axis) {
        Set<String> out = new TreeSet<>();
        for (JsonNode reading : readingsOn(report, axis)) {
            out.add(reading.path("against").asString());
        }
        return out;
    }

    /** The values on {@code axis} a row of the examples met. */
    private static Set<String> pointsMetOn(JsonNode report, String axis) {
        Set<String> out = new TreeSet<>();
        for (JsonNode reading : readingsOn(report, axis)) {
            if (reading.path("hit").asBoolean()) {
                out.add(reading.path("against").asString());
            }
        }
        return out;
    }

    private static List<JsonNode> readingsOn(JsonNode report, String axis) {
        List<JsonNode> out = new ArrayList<>();
        collect(report, axis, out);
        return out;
    }

    /** The rows owed at a line and beside it, and not those owed in the runs between lines. */
    private static void collect(JsonNode node, String axis, List<JsonNode> out) {
        if (node.isObject() && node.has("point") && node.has("readings")
                && "part_of_comparison".equals(
                        node.at("/obligationId/line/which/kind").asString())
                && Set.of("at_the_line", "beside_the_line").contains(
                        node.at("/obligationId/location/kind").asString())) {
            JsonNode reading = node.path("readings").get(0);
            if (reading.path("axis").asString().equals(axis)) {
                out.add(reading);
            }
        }
        node.forEach(child -> collect(child, axis, out));
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

    private static JsonNode reportOf(String model, String examples) {
        Compilation compilation = Compilation.ofSource(model + "\n" + examples, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "compiles: " + compilation.errors());
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }
}
