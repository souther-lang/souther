package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

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
        String report = human(model);
        assertFalse(report.contains("not read"), report);
        assertFalse(report.contains(SUCH_A_RUN_STOPS), report);
    }

    /**
     * Where every run that reaches the comparison stops, wherever in it the operation stands, the
     * comparison is read to the end and has no line; it is not several lines held together nor a
     * form this compiler does not read.
     */
    @Test
    void aComparisonEveryRunOfWhichStopsIsReadToTheEndAndHasNoLine() {
        for (String guard : List.of("a / 0 >= k", "a / 0 + b >= k", "(a / 0) * b >= k",
                "a >= k / 0", "-(a / 0) >= k", "(a / 0 >= k) || k > 0")) {
            String report = human(MODEL.formatted("", guard));
            assertTrue(report.contains(SUCH_A_RUN_STOPS), guard + "\n" + report);
            assertFalse(report.contains("several lines held together"), guard + "\n" + report);
            assertFalse(report.contains("written in a form this compiler does not read"),
                    guard + "\n" + report);
        }
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
