package souther.compiler;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule compared against a constant a fold reaches is the rule it states with that constant worked
 * out.
 *
 * <p>The walk that reads a comparison composes over the operators that are linear in the positions
 * they are written over. What it does with the rest is ask what an expression it composed nothing out
 * of folds to, so an operation over written values is read without that operation being arithmetic
 * over positions — which it is not, and which none of these makes it.
 *
 * <p>And what the fold declines leaves the rule unread, beside a control that differs from it in the
 * operation alone. A reading that answered everything and a reading that answered nothing would both
 * pass a set with only the first half.
 */
class AConstantAFoldReachesIsTheNumberItIsWrittenInPlaceOfTest {

    private static String overOne(String type, String guard) {
        return """
                module m

                behavior f : (x: %s) -> Bool

                let f (x) = {
                    guard %s else false

                    true
                }
                """.formatted(type, guard);
    }

    /**
     * What a model's rules came to: the lines they drew, and what they left unread with the reason
     * the position was left with.
     *
     * <p>Both, always, because a line nobody drew and a rule nobody read are two answers and the
     * difference between them is what this whole measure is about. Read off the drawn lines alone,
     * a rule this stopped reading for some other reason would pass for a quotient it declined to
     * fold.
     */
    private record Measured(List<String> lines, List<String> notRead) {}

    private static Measured measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream().map(e -> e.diagnostic().code()).toList(),
                "the model under test compiles");
        AdequacyReport.BehaviorReport behavior =
                AdequacyReport.of(compilation).modules().get(0).behaviors().get(0);
        return new Measured(
                behavior.lines().stream().map(BorderAssessment::value).toList(),
                behavior.partition().notRead().stream()
                        .map(each -> each.at() + ": " + each.reason()).toList());
    }

    /**
     * The lines a model's rules draw, by the value each is drawn at — of a model whose rule divides
     * the position it names, so that nothing is left unread and the lines are the whole answer.
     *
     * <p>A rule relating two positions divides neither and says so, which is a different answer
     * from this one; the models written that way are compared whole ({@link #measured}) rather than
     * through here.
     */
    private static List<String> lines(String source) {
        Measured measured = measured(source);
        assertEquals(List.of(), measured.notRead(), "every rule of the model was read");
        return measured.lines();
    }

    /** What a model whose rule this could not read is left with, which is the rule reported unread
     *  and no line anywhere. */
    private static void unread(String source) {
        Measured measured = measured(source);
        assertEquals(List.of("x: UNSUPPORTED_SYNTAX"), measured.notRead());
        assertEquals(List.of(), measured.lines());
    }

    /**
     * An operation over written numbers that the fold does not compute leaves the rule unread, and
     * the rule states what it always stated.
     *
     * <p>Beside the same number written out, so the two differ in the operation alone: a rounding to
     * the place a number already sits at is that number, and what leaves the rule unread is that
     * nothing here computes the rounding.
     */
    @Test
    void anOperationTheFoldDoesNotComputeLeavesTheRuleUnread() {
        unread(overOne("Decimal", "x < Decimal.round(1, HALF_UP, 3.5m)"));
        assertEquals(List.of("3.5"), lines(overOne("Decimal", "x < 3.5m")));
    }

    /**
     * What a call folds to is still read, which is the question this walk was already asking before
     * it asked it of anything else.
     */
    @Test
    void aCallThatFoldsIsStillTheNumberItFoldsTo() {
        List<String> lines = lines("""
                module m

                behavior f : (s: String) -> Bool

                let f (s) = {
                    guard String.length(s) < String.length("1A") else false

                    true
                }
                """);

        assertEquals(List.of("2"), lines);
    }
}
