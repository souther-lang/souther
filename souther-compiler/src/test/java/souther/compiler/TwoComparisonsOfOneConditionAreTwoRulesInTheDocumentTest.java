package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleCitation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two comparisons of one condition are two rules, and a document says so.
 *
 * <p>{@code RuleRef} states it: a comparison is the rule and the fork testing it is not, so one
 * condition holding two of them holds two rules. What a reader is given for a rule with no name is
 * where it is written — and that was the fork's place, so both came out under one handle. Two
 * questions about one position, with the same rule, the same question and the same subject: a
 * consumer cannot tell two rules asking alike from one question written twice.
 *
 * <p>The other half of the same contract is that one rule read twice is one question. Nothing
 * observes it: a comparison inside a helper reaches this accounting not at all, which is what the
 * second test writes down.
 */
class TwoComparisonsOfOneConditionAreTwoRulesInTheDocumentTest {

    private static List<PartitionEvidence.Unanswered> standing(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .modules().get(0).behaviors().get(0).partition().unanswered();
    }

    /** Where each rule is written, which is what a rule with no name is found by. */
    private static Set<String> placesIn(List<PartitionEvidence.Unanswered> standing) {
        return standing.stream()
                .map(each -> ((RuleCitation.WrittenAt) each.cited()).at().toString())
                .collect(java.util.stream.Collectors.toCollection(java.util.LinkedHashSet::new));
    }

    /**
     * Two bounds on one position, neither of which this compiler can fold.
     *
     * <p>One position and one question each, so nothing else in the entry tells them apart: the
     * citation is the whole of the difference.
     */
    @Test
    void twoComparisonsAboutOnePositionAreTwoQuestionsWithTwoPlaces() {
        List<PartitionEvidence.Unanswered> standing = standing("""
                module m

                data R = { a: Int }
                data X
                data Y

                behavior f : (r: R) -> X | Y
                    constructs X, Y
                let f (r) = if r.a <= 10 * 2 && r.a >= 20 * 2 then X else Y

                example f
                    | "one" : (R { a = 1 }) -> Y
                """);

        assertEquals(4, standing.size(),
                () -> "two rules, a border and its classes each: " + standing);
        assertEquals(2, placesIn(standing).size(),
                () -> "and two places to look, not one twice: " + standing);
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
                    constructs X, Y
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
