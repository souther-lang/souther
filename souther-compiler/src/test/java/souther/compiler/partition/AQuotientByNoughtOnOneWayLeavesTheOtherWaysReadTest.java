package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A way that divides by nought is no row of either side of the comparison, so the ways that do not
 * divide by nought are read as they would be alone.
 */
class AQuotientByNoughtOnOneWayLeavesTheOtherWaysReadTest {

    private static final String GUARDED = """
            module demo

            data Ok
            data No

            behavior f : (k: Int, a: Int) -> Ok | No
            let f (k, a) = {
                guard a > 0 else No
                guard (if a > 0 then a else 0) / (if a > 0 then 1 else 0) >= k else No
                Ok
            }
            """;

    @Test
    void aWayThatAnEarlierGuardRulesOutLeavesNothingUnread() {
        String report = human(GUARDED);
        assertFalse(report.contains("not read"), report);
    }

    private static final String UNGUARDED = """
            module demo

            data Ok
            data No

            behavior f : (k: Int, a: Int) -> Ok | No
            let f (k, a) = {
                guard (if a > 0 then a else 0) / (if a > 0 then 1 else 0) >= k else No
                Ok
            }
            """;

    private static final String MEAN = """
            module demo

            data Ok
            data No

            behavior f : (k: Int, a: Int, b: Int) -> Ok | No
            let f (k, a, b) = {
                let xs = List.filter(x -> x > 0, [a, b])
                guard List.length(xs) > 0 else No
                guard List.sum(xs) / List.length(xs) >= k else No
                Ok
            }
            """;

    private static final String SUM = MEAN.replace("List.sum(xs) / List.length(xs) >= k",
            "List.sum(xs) >= k");

    /** Without the guard the way that divides by nought is no row, and the other way is read. */
    @Test
    void theWayThatDividesByNoughtIsNoRowWhereNothingRulesItOut() {
        String report = human(UNGUARDED);
        assertFalse(report.contains("not read"), report);
        assertFalse(report.contains("quotient by nought"), report);
    }

    /**
     * The mean is read as far as the sum is: what is left unsaid of it is what is left unsaid of a
     * sum beside a number, and the count of the list in the way it holds nothing is no stop.
     */
    @Test
    void aMeanOverAFilteredListIsUnreadForNoReasonTheSumIsNot() {
        String mean = human(MEAN);
        assertFalse(mean.contains("quotient by nought"), mean);
        assertEquals(notReadWithoutPositions(human(SUM)), notReadWithoutPositions(mean));
    }

    private static Set<String> notReadWithoutPositions(String report) {
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
