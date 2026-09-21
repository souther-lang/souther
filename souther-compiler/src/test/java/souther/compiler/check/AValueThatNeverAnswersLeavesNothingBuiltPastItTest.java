package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.core.Core;
import souther.compiler.coverage.Arrivals;
import souther.compiler.query.Bodies;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a build of a value comes to is what the value's template does, so where the value never
 * answers, nothing that needs its answer is reached.
 *
 * <p>A build stands for the evaluation of the value, and that evaluation may end in an abort
 * instead of an answer. Read as a leaf that always yields a value, the build reaches the code after
 * it, and the readings that ask whether a run arrives — which arm is taken, whether an expression
 * answers a value — would count what no run gets to.
 */
class AValueThatNeverAnswersLeavesNothingBuiltPastItTest {

    private static AnalysisBody analysed(String value, String declared) {
        return Compiler.compiled("""
                module m exposing (f)

                let never%s = %s

                behavior f : (n: Int) -> Int
                let f (n) = never
                """.formatted(declared, value), "m").db()
                .ask(new Bodies.Checked("m")).value().analysisBodies().get("f");
    }

    private static boolean answers(AnalysisBody analysis) {
        Core body = analysis.core();
        return Arrivals.inTheTree(body, analysis.templates()::bodyOf).at(body);
    }

    @Test
    void aBodyThatIsAValueThatNeverAnswersAnswersNothing() {
        assertFalse(answers(analysed("unreachable \"this value has no answer\"", ": Int")),
                "the value ends in an abort, so a run never arrives at a value by way of it");
    }

    @Test
    void aBodyThatIsAValueThatAnswersAnswers() {
        assertTrue(answers(analysed("if true then 1 else 2", "")),
                "and one that answers is one a run arrives at");
    }
}
