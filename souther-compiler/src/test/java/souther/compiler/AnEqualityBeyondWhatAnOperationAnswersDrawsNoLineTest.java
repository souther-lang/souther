package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule that names a value its quantity never takes draws no line, whichever way it names it.
 *
 * <p>An order across a line and an equation at a value are both dropped where the quantity stops
 * short of the line, and the measure says so at the rule. A number an operation bounds is where it
 * shows, since no rule about it says how far it runs.
 */
class AnEqualityBeyondWhatAnOperationAnswersDrawsNoLineTest {

    private static String about(String parameter, String body) {
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (%s) -> Bool
                let f (x) = %s
                """.formatted(parameter, body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void anHourNoTimeHasIsNoLine() {
        for (String body : new String[] {"Time.hour(x) == 30", "Time.hour(x) /= 30",
                "Time.hour(x) == -1"}) {
            String report = about("x: Time", body);

            assertTrue(report.contains("measurement: complete"), body + "\n" + report);
            assertTrue(report.contains("draws its line outside what the quantity it cuts"),
                    body + "\n" + report);
        }
    }

    @Test
    void aYearNoDateHasIsNoLine() {
        for (String body : new String[] {"Date.year(x) == 1000000000",
                "Date.year(x) /= -1000000000"}) {
            String report = about("x: Date", body);

            assertTrue(report.contains("measurement: complete"), body + "\n" + report);
            assertTrue(report.contains("draws its line outside what the quantity it cuts"),
                    body + "\n" + report);
        }
    }

    @Test
    void anHourATimeHasStillDrawsItsLine() {
        String report = about("x: Time", "Time.hour(x) == 13");

        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("draws its line outside"), report);
        assertTrue(report.contains("= 13"), report);
    }
}
