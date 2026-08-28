package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard the declarations leave no room for is one answer everywhere it is read.
 *
 * <p>Three measures look at the same comparison, and a model where its satisfying side holds nothing
 * has to come to one thing in all of them: the arm behind it is one no row reaches, the line it
 * would draw is not there, and the declaration's own line at the same value still is. Read apart,
 * one of them would ask for a row on a side no value stands on while another proved nothing stands
 * there.
 *
 * <p><b>The declaration's line is what makes this a test rather than a way of saying nothing.</b> A
 * reading that dropped every line at the value would pass the absences below and be plainly wrong;
 * what is asked is that the comparison's line goes and the clause's stays.
 *
 * <p>Only a proof takes anything away. What no value of the input reaches is what a walk of the
 * paths proves, and what it leaves unproved keeps everything — an absent proof is not a proof of
 * absence. The line the comparison drew is not dropped either: it is disposed of under that proof,
 * and every piece of evidence this stage takes in leaves it with one, which is what keeps a line
 * from going missing rather than anything written here.
 */
class AGuardTheDeclarationsCannotSatisfyIsOneUnreachableAnswerTest {

    private static final String MODULE = "example.noroom";

    /**
     * The rules stop the position at ten and up, and the body asks whether it is under ten.
     *
     * <p>So the {@code then} arm is one no value of the input reaches, and the ten the comparison
     * names is a value the declaration already draws its own line at.
     */
    private static final String MODEL = """
            module example.noroom

            data Level = Int
                invariant value >= 10

            data Answer = { n: Int }

            behavior classify : (level: Level) -> Answer
                constructs Answer

            let classify (level) =
                if level.value < 10 then Answer { n = 1 } else Answer { n = 2 }
            """;

    private static String report() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String human = AdequacyReport.of(compilation).human(SourceNameResolver.identity());
        // A report over nothing would pass every absence asked of it below, so the model is held to
        // having been measured at all before anything is read off it.
        assertTrue(human.contains("classify"),
                () -> "the model under test compiles and is measured: " + human + " / "
                        + compilation.diagnostics()
                                .getOrDefault(new souther.compiler.source.SourceId("0"),
                                        java.util.List.of())
                                .stream().map(each -> each.diagnostic().code()
                                        + "@" + each.diagnostic().primary()).toList());
        return human;
    }

    /** No row is asked for on the side it is satisfied, because no value of the position is there. */
    @Test
    void noRowIsAskedForOnTheSideItIsSatisfied() {
        assertFalse(report().contains("classify/level"),
                () -> "the comparison draws no line of its own: " + report());
        assertFalse(report().contains("no row goes through `then`"),
                () -> "nor is the arm behind it asked for: " + report());
    }

    /**
     * And the declaration's line at the same value is still there, still owing its row.
     *
     * <p>Which is what says the two were told apart rather than dropped together. A reading that
     * dropped every line at ten would pass everything above and be plainly wrong.
     */
    @Test
    void theDeclarationsOwnLineAtThatValueIsStillDrawn() {
        assertTrue(report().contains("at level = 10 (invariant Level #1)"),
                () -> "the clause's own end is a line whatever the body asks: " + report());
        assertTrue(report().contains("border      borders 1"),
                () -> "and it is the only line here: " + report());
    }
}
