package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * One rule read twice is one question, and nothing observes it.
 *
 * <p>{@code RuleRef} says a comparison inside a helper is read once per call and is one rule all the
 * same, and the questions are folded by rule before they are published. No input is known that
 * reaches that fold: a comparison written in a helper raises nothing at all, which is what this
 * writes down. That two rules stay two is asked of the document
 * ({@link TwoRulesAskingAlikeStayTwoInTheDocumentTest}).
 */
class AComparisonInsideAHelperRaisesNothingTest {

    private static List<PartitionEvidence.Unanswered> standing(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .modules().get(0).behaviors().get(0).partition().unanswered();
    }

    /**
     * A comparison written in a helper raises nothing at all, however often it is reached.
     *
     * <p>Written down because it is what happens and not what should. The other half of
     * {@code RuleRef}'s contract is that one rule read twice is one question, and the fold that
     * holds it is unobserved: no input is known that reaches this accounting from inside a helper,
     * so removing the fold leaves every test green. This is what an input that would have reached it
     * does instead.
     *
     * <p>Which is its own gap — a comparison an author wrote is a rule of the model wherever they
     * wrote it — and not this issue's. Asserted so that the day it stops being true, what a document
     * does with two readings of one rule has to be decided rather than discovered.
     */
    @Test
    void aComparisonInsideAHelperRaisesNothingToday() {
        String model = """
                module m

                data R = { a: Int, b: Int }
                data X
                data Y

                let big (n: Int) = n <= 10 * 2

                behavior f : (r: R) -> X | Y
                let f (r) = %s

                example f
                    | "one" : (R { a = 1, b = 1 }) -> X
                """;

        assertEquals(List.of(), standing(model.formatted("if big(r.a) then X else Y")),
                "reached once");
        assertEquals(List.of(),
                standing(model.formatted("if big(r.a) then X else if big(r.b) then X else Y")),
                "and reached twice");
    }
}
