package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code n <= k} and the same comparison with a sum worked out beside {@code n} that comes past
 * the greatest {@code Int} whatever the input is: the relation is the same, and the program stops
 * before it is compared. What the relation says of two numbers is not what the program does with
 * them, so the report says no row gets to the line, and does not say the two numbers divide
 * nothing.
 */
class AComparisonThatCannotRunIsNotShownDividedNoWayTest {

    private static String report(String body) {
        String model = """
                module probe.m

                data Yes
                data No

                behavior f : (m: Int, n: Int, k: Int) -> Yes | No
                let f (m, n, k) = if %s <= k then Yes else No
                """.formatted(body);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    @Test
    void aComparisonThatCanRunRelatesTheTwoNumbers() {
        String report = report("n");

        assertTrue(report.contains("relates the value here to another value"), report);
    }

    @Test
    void aComparisonWhoseProgramStopsBeforeItIsComparedHasNoRowAtItsLine() {
        String report = report("(m - m) + 9223372036854775807 + 1 - 1 + n");

        assertTrue(report.contains("rules those values out"), report);
        assertFalse(report.contains("divided no way: n"), report);
        assertFalse(report.contains("divided no way: k"), report);
        assertFalse(report.contains("relates the value here to another value"), report);
    }
}
