package souther.compiler;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule compared against a quotient of written numbers is the rule it states with that quotient
 * worked out.
 *
 * <p>The walk that reads a comparison composes over the operators that are linear in the positions
 * they are written over, and a truncating divide is not one of them. What it does instead is ask
 * what an expression it composed nothing out of folds to, so a divide of two written numbers is
 * read without a divide being arithmetic over positions — which it is not, and which none of these
 * makes it.
 *
 * <p>Both ways a constant reaches a rule are here, because they are two ways to write one thing and
 * a model reaches the second by writing a fraction where a coefficient belongs. Each is held
 * against the rule it comes to: the quotient is read exactly where the line it draws is the line
 * the worked-out number draws.
 *
 * <p>And what the fold declines leaves the rule unread, each beside a control that differs from it
 * in the divisor alone. A reading that answered everything and a reading that answered nothing
 * would both pass a set with only the first half.
 */
class AConstantQuotientIsTheNumberItIsWrittenInPlaceOfTest {

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

    private static String overTwo(String guard) {
        return """
                module m

                behavior f : (x: Int, y: Int) -> Bool

                let f (x, y) = {
                    guard %s else false

                    true
                }
                """.formatted(guard);
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

    /** A quotient standing where a bound belongs draws the line its value draws. */
    @Test
    void aQuotientWrittenAsABoundIsTheLineItsValueDraws() {
        assertEquals(lines(overOne("Int", "x < 3")), lines(overOne("Int", "x < 7 / 2")));
        assertEquals(List.of("3"), lines(overOne("Int", "x < 7 / 2")));
    }

    /**
     * Toward nought, which is where a whole-number divide rounds. The line falls at {@code -1} and
     * not at {@code -2}, so a reading that floored the quotient is told from this one.
     */
    @Test
    void aNegativeQuotientDrawsTheLineTruncationLeaves() {
        assertEquals(lines(overOne("Int", "x < -1")), lines(overOne("Int", "x < -3 / 2")));
        assertEquals(List.of("-1"), lines(overOne("Int", "x < -3 / 2")));
    }

    /**
     * The same constant reaching the rule as a coefficient, which is how a model writes a line of
     * fractional slope.
     *
     * <p>Both quotients, because over whole numbers the second is nought: a coefficient that folds
     * to nought is a coefficient that vanishes, and a line read from that alone says nothing about
     * whether the quotient was read at all. The first carries it.
     */
    @Test
    void aQuotientWrittenAsACoefficientIsTheNumberItMultipliesBy() {
        Measured carried = measured(overTwo("y < 3 / 2 * x + 30"));
        Measured vanished = measured(overTwo("y < -1 / 2 * x + 30"));

        assertEquals(measured(overTwo("y < x + 30")), carried);
        assertEquals(List.of("x + 30"), carried.lines());
        assertEquals(measured(overTwo("y < 30")), vanished);
        assertEquals(List.of("30"), vanished.lines());
    }

    /** Nothing is divided by nought, so the rule is left where a rule this cannot read is left. */
    @Test
    void aDivisorOfNoughtLeavesTheRuleUnread() {
        unread(overOne("Int", "x < 7 / 0"));
        assertEquals(List.of("7"), lines(overOne("Int", "x < 7 / 1")));
    }

    /**
     * The quotient whose value is outside the range an {@code Int} holds. The control divides the
     * same dividend by one, so what is read here is the quotient and not the size of the number
     * written.
     */
    @Test
    void theQuotientOutsideTheRangeAnIntHoldsLeavesTheRuleUnread() {
        String least = "(0 - 9223372036854775807 - 1)";

        unread(overOne("Int", "x < " + least + " / -1"));
        assertEquals(List.of("-9223372036854775808"), lines(overOne("Int", "x < " + least + " / 1")));
    }

    /** A {@code Decimal} divide is answered by the run time at a scale this does not hold, and the
     *  rule states what it always stated. */
    @Test
    void aDecimalDivideLeavesTheRuleUnread() {
        unread(overOne("Decimal", "x < 7.0m / 2.0m"));
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
