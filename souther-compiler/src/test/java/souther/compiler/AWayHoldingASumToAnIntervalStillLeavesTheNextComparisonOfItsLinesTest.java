package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard on a sum holds the numbers it adds to an interval, and the guard after it is read there:
 * a row at the line of the second guard has the sum within a step of the line, which the first
 * holds it to, so the first ties the numbers to one another by nothing that row needs.
 *
 * <p>A way holding the numbers to another form ties them, and the guard after it is still said
 * not to be read.
 */
class AWayHoldingASumToAnIntervalStillLeavesTheNextComparisonOfItsLinesTest {

    private static final String NOT_READ = "· not read: comparison";

    private static String model(String guards) {
        return """
                module example.band

                data Low
                data Mid
                data High

                behavior band : (a: Int, b: Int) -> Low | Mid | High

                let band (a, b) = {
                %s
                    Mid
                }
                """.formatted(guards);
    }

    private static String report(String guards) {
        String source = model(guards);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(), source);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The first guard alone is read, and the second beside it is read to the same lines. */
    @Test
    void aSecondGuardOnTheSameSumIsReadBesideTheFirst() {
        String first = "    guard a + b >= 100 else Low";
        String alone = report(first);
        assertFalse(alone.contains(NOT_READ), alone);
        String both = report(first + "\n    guard a + b < 200 else High");
        assertFalse(both.contains(NOT_READ), both);
        assertTrue(both.contains("borders 2"), both);
    }

    /** The same holds from the other end, and with the strict side of each line the other way. */
    @Test
    void theOrderOfTheTwoGuardsAndTheSideOfEachLineDoNotMatter() {
        for (String guards : List.of(
                "    guard a + b < 200 else High\n    guard a + b >= 100 else Low",
                "    guard a + b > 99 else Low\n    guard a + b <= 199 else High")) {
            String report = report(guards);
            assertFalse(report.contains(NOT_READ), guards + "\n" + report);
        }
    }

    /** A way that holds the numbers to another form ties them, and says nothing a row at the line
     *  of the sum could meet. */
    @Test
    void aWayHoldingAnotherFormStillTiesTheNumbers() {
        String report = report("    guard a - b >= 0 else Low\n    guard a + b < 200 else High");
        assertTrue(report.contains(NOT_READ), report);
    }
}
