package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule that compares a number of a string with one past what a String holds owes no point on
 * the side no String reaches.
 *
 * <p>A String holds no more than 268435455 code points, so a length never passes what that comes
 * to. That is where the values stop and not a distinction a model made: the values beyond it are
 * not held as a range of lengths no value has.
 */
class ALineBeyondWhatAStringHoldsIsNoLineTest {

    private static String about(String body) {
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (s: String) -> Bool
                let f (s) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void noPointIsOwedAtALengthPastTheLongestString() {
        for (String body : new String[] {"String.length(s) >= 268435456",
                "String.length(s) > 268435455"}) {
            String report = about(body);

            assertTrue(report.contains("no ON point is owed"), body + "\n" + report);
            assertTrue(report.contains("no IN point is owed"), body + "\n" + report);
            assertTrue(report.contains("no value can stand there"), body + "\n" + report);
        }
    }

    @Test
    void aLengthFarPastTheLongestStringIsNoLineAtAll() {
        String report = about("String.length(s) >= 1000000000");

        assertTrue(report.contains("draws its line outside what the quantity it cuts"), report);
    }

    @Test
    void aLineThatCannotBeReachedTakesNothingFromTheOneBesideIt() {
        String report = about("if String.length(s) >= 268435456 then true"
                + " else String.length(s) >= 3");

        assertTrue(report.contains("no ON point is owed at String.length(s) = 268435456"), report);
        assertTrue(report.contains("= 3"), report);
    }

    @Test
    void theLongestStringIsAValueOfTheLengthAtItsEnd() {
        String report = about("String.length(s) >= 268435455");

        assertFalse(report.contains("no ON point is owed"), report);
    }

    @Test
    void aLengthBelowTheLongestStringStillOwesItsPoints() {
        String report = about("String.length(s) >= 3");

        assertFalse(report.contains("no value can stand there"), report);
        assertTrue(report.contains("= 3"), report);
    }
}
