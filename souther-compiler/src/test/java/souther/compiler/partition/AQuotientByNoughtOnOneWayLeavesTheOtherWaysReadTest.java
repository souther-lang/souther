package souther.compiler.partition;

import org.junit.jupiter.api.Test;

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
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way that divides by nought is no row of either side of the comparison, so the ways that do not
 * divide by nought are read as they would be alone, and a comparison every run of which stops in
 * such an operation is said to be one, and not a rule this compiler could not read.
 */
class AQuotientByNoughtOnOneWayLeavesTheOtherWaysReadTest {

    private static final String MODEL = """
            module demo

            data Ok
            data No

            behavior f : (k: Int, a: Int, b: Int) -> Ok | No
            let f (k, a, b) = {
                %s
                guard %s else No
                Ok
            }
            """;

    private static final String ABOVE = "guard a > 0 else No";

    /** The divisor is nought on the way where {@code a} is not above nought. */
    private static final String QUOTIENT =
            "(if a > 0 then a else 0) / (if a > 0 then 1 else 0) >= k";

    private static final String SUCH_A_RUN_STOPS = "stops in an operation it is read through";

    /** The line a comparison of two values draws is the line between them. */
    private static List<String> lineBetweenAAndK(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return Adequacy.readingsOf(compilation.db(), "demo").get("f").stream()
                .filter(line -> line.border().cut().toString().contains("Apart"))
                .map(line -> (line.border().cut() + " " + new TreeSet<>(line.items().keySet()
                        .stream().map(String::valueOf).toList())))
                .toList();
    }

    /**
     * Under a guard that rules the way out, the comparison is the comparison of the way that
     * divides by something else: the line between {@code a} and {@code k}, with the sides and the
     * points it has when it is written as {@code a >= k}.
     */
    @Test
    void underAGuardTheComparisonDrawsTheLineOfTheWayThatAnswers() {
        List<String> written = lineBetweenAAndK(MODEL.formatted(ABOVE, "a >= k"));
        assertEquals(1, written.size(), written.toString());
        assertEquals(written, lineBetweenAAndK(MODEL.formatted(ABOVE, QUOTIENT)));
        assertFalse(human(MODEL.formatted(ABOVE, QUOTIENT)).contains("not read"));
    }

    /** Without the guard the way that divides by nought is no row, and the line is the same. */
    @Test
    void withoutAGuardTheWayThatAnswersDrawsTheSameLine() {
        List<String> written = lineBetweenAAndK(MODEL.formatted(ABOVE, "a >= k"));
        String model = MODEL.formatted("", QUOTIENT);
        assertEquals(written, lineBetweenAAndK(model));
        assertFalse(human(model).contains("not read"));
    }

    /**
     * Where every run that reaches the comparison stops, wherever in it the operation stands, the
     * comparison is read to the end and has no line; it is not several lines held together nor a
     * form this compiler does not read.
     */
    @Test
    void aComparisonEveryRunOfWhichStopsIsReadToTheEndAndHasNoLine() {
        for (String guard : List.of("a / 0 >= k", "a / 0 + b >= k", "(a / 0) * b >= k",
                "a >= k / 0", "-(a / 0) >= k", "(a / 0 >= k) || k > 0",
                // And through the total of a list the body wrote out, kept or not.
                "List.sum([a / 0, b / 1]) >= k",
                "List.sum(List.filter(x -> x > 0, [a / 0, b / 1])) >= k",
                "List.sum(List.map(x -> x / 0, [a, b])) >= k")) {
            String report = human(MODEL.formatted("", guard));
            assertTrue(report.contains(SUCH_A_RUN_STOPS), guard + "\n" + report);
            assertFalse(report.contains("several lines held together"), guard + "\n" + report);
            assertFalse(report.contains("written in a form this compiler does not read"),
                    guard + "\n" + report);
        }
    }

    private static final String A_RUN_STOPS = "run stops:";

    /**
     * Without the guard, the way that divides by nought is a place where a run stops, said beside
     * the line the other way draws and not instead of it.
     */
    @Test
    void withoutAGuardTheWayThatStopsIsSaidBesideTheLineTheOtherWayDraws() {
        String report = human(MODEL.formatted("", QUOTIENT));
        assertTrue(report.contains(A_RUN_STOPS), report);
        assertFalse(report.contains("not read"), report);
        assertEquals(1, lineBetweenAAndK(MODEL.formatted("", QUOTIENT)).size());
    }

    /** Under the guard no row takes the way that divides by nought, and nothing is said of it. */
    @Test
    void underAGuardThatRulesTheWayOutNoRunStopsAndNothingIsSaid() {
        assertFalse(human(MODEL.formatted(ABOVE, QUOTIENT)).contains(A_RUN_STOPS));
    }

    /**
     * A stop no guard rules out is said wherever it stands in the comparison, and by the same
     * words however the comparison is written.
     */
    @Test
    void aStopOnSomeWaysIsSaidWhereverItStandsInTheComparison() {
        for (String guard : List.of("(if a > 0 then a / 0 else b / 1) >= k",
                "(if a > 0 then a / 1 else b / 0) >= k",
                "a / 1 + (if b > 0 then 1 / 1 else 1 / 0) >= k")) {
            String report = human(MODEL.formatted("", guard));
            assertTrue(report.contains(A_RUN_STOPS), guard + "\n" + report);
            assertFalse(report.contains("not read"), guard + "\n" + report);
        }
    }

    private static final String MATCHED =
            "(match (if a > 0 then Ok else No) with | Ok -> a / 1 | No -> a / 0) >= k";

    /**
     * An arm of a {@code match} that stops is down only where the arm is taken: under a guard that
     * rules the arm out no run stops, and without it some do.
     */
    @Test
    void anArmOfAMatchStopsARunOnlyWhereTheArmIsTaken() {
        assertFalse(human(MODEL.formatted(ABOVE, MATCHED)).contains(A_RUN_STOPS));
        assertTrue(human(MODEL.formatted("", MATCHED)).contains(A_RUN_STOPS));
    }

    /**
     * The finding is about a rule, and names it by the identity the document gives every rule a
     * finding is about.
     */
    @Test
    void aRuleSomeRunsStopInIsNamedByItsRuleIdInTheDocument() {
        Compilation compilation = Compilation.ofSource(MODEL.formatted("", QUOTIENT), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        JsonNode findings = JsonMapper.builder().build()
                .readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0).get("findings");
        List<JsonNode> stopping = new ArrayList<>();
        for (JsonNode each : findings) {
            if (each.get("kind").asString().equals("rule_stops_some_runs")) {
                stopping.add(each);
            }
        }
        assertEquals(1, stopping.size(), findings.toString());
        assertTrue(stopping.getFirst().has("ruleId"), stopping.getFirst().toString());
        assertFalse(stopping.getFirst().has("reason"), stopping.getFirst().toString());
    }

    /** A comparison every run stops in is said once, as one that draws no line. */
    @Test
    void aComparisonEveryRunStopsInIsNotSaidTwice() {
        String report = human(MODEL.formatted("", "a / 0 >= k"));
        assertFalse(report.contains(A_RUN_STOPS), report);
        assertTrue(report.contains(SUCH_A_RUN_STOPS), report);
    }

    private static final String ALL = """
            module demo

            data Ok
            data No

            behavior f : (k: Int) -> Ok | No
            let f (k) = {
                guard List.all(d -> 10 / d >= k, %s) else No
                Ok
            }
            """;

    /**
     * One closure made on two values, one of them nought: the application that divides by
     * nought is a stop and the other draws its line, and neither is lost to the other.
     */
    @Test
    void aClosureMadeOnTwoValuesOneOfWhichStopsSaysBoth() {
        String report = human(ALL.formatted("[1, 0]"));
        assertTrue(report.contains(A_RUN_STOPS), report);
        assertFalse(human(ALL.formatted("[1, 2]")).contains(A_RUN_STOPS));
    }

    /**
     * The application that stops is not folded into the one that settles the same for every row:
     * the comparison cuts nothing where a run gets past it, and some runs do not get past it.
     */
    @Test
    void anApplicationThatStopsIsNotLostToOneThatCutsNothing() {
        String model = ALL.replace("10 / d >= k", "10 / d >= 1");
        String report = human(model.formatted("[1, 0]"));
        assertTrue(report.contains(A_RUN_STOPS), report);
        assertFalse(human(model.formatted("[1, 2]")).contains(A_RUN_STOPS));
    }

    /** The reason is the stop's, not the reading's: a division by nought stops the run. */
    @Test
    void aComparisonThatStopsEveryRunIsNotAnythingThatStopsOnlyTheReading() {
        String report = human(MODEL.formatted("", "a / 0 >= k"));
        assertFalse(report.contains("quotient by nought"), report);
        assertTrue(report.contains("no line:"), report);
        assertFalse(report.contains("not read:"), report);
    }

    /** What is unread for another reason on the way that answers stays unread for that reason. */
    @Test
    void whatIsUnreadForAnotherReasonOnTheWayThatAnswersIsStillSaidForThatReason() {
        String report = human(MODEL.formatted("",
                "(if a > 0 then a * a else 0) / (if a > 0 then 1 else 0) >= k"));
        assertTrue(report.contains("a product of two values that are not constants"), report);
        assertFalse(report.contains(SUCH_A_RUN_STOPS), report);
    }

    private static final String LIST = """
            module demo

            data Ok
            data No

            behavior f : (k: Int, a: Int, b: Int) -> Ok | No
            let f (k, a, b) = {
                let xs = List.filter(x -> x > 0, [a, b])
                guard List.length(xs) > 0 else No
                guard %s >= k else No
                Ok
            }
            """;

    /**
     * A mean over a list the body wrote out is read as far as the sum of it is: the way where the
     * list holds nothing divides by nought and is no row, and what is left unsaid is what the sum
     * beside a number leaves unsaid, which is a fact of its own and not about the quotient.
     */
    @Test
    void aMeanOverAFilteredListIsUnreadForNoReasonItsSumIsNot() {
        String mean = human(LIST.formatted("List.sum(xs) / List.length(xs)"));
        String sum = human(LIST.formatted("List.sum(xs)"));
        assertFalse(mean.contains("quotient by nought"), mean);
        assertFalse(notRead(sum).isEmpty(), sum);
        assertEquals(notRead(sum), notRead(mean));
        assertTrue(mean.contains("border      borders"), mean);
    }

    private static Set<String> notRead(String report) {
        return report.lines()
                .filter(line -> line.contains("not read:"))
                .map(line -> line.replaceAll("@\\d+:\\d+", ""))
                .collect(Collectors.toSet());
    }

    private static String human(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
