package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line on a field every case of a sum spreads is drawn at each case whose own rules leave the
 * field running as far as the line, and said to be outside at each case whose rules do not.
 *
 * <p>The field is one name and as many quantities as there are cases. {@code r.deadline > 10} is a
 * line the field reaches, since the cases between them hold every value up to a hundred; a case whose
 * invariant holds its deadline to five never gets there, and neither does one that holds it above
 * twenty from the other side — there the line is below everything the case holds. Each of those is a
 * quantity the line is outside of, said at that quantity in the words a line outside the field itself
 * is said in, while the case that reaches it keeps its border.
 */
class ALineACaseNeverReachesIsSaidAtThatCaseTest {

    /** {@code P} with the invariant given, {@code Q} with the one given, and a guard at ten. */
    private static String guarded(String p, String q, String guard, String row) {
        return """
                module probe.r exposing ( C, R, P, Q, S, f )

                data C = { deadline: Int }
                    invariant deadline >= 0 && deadline <= 100

                data P = { ...C }
                %s

                data Q = { ...C }
                %s

                data R = P | Q

                data S = { n: Int }
                    invariant n >= 0 && n <= 1

                behavior f : (r: R, s: S) -> Int

                let f (r, s) = if %s then 1 else 0

                example f
                    | "one" : (%s, S { n = 0 }) -> 0
                """.formatted(p, q, guard, row);
    }

    private static String atTen(String p) {
        return guarded(p, "", "r.deadline > 10", "Q { deadline = 3 }");
    }

    /** What a report says of a rule at a quantity its line is outside of. */
    private static String outsideAt(String position) {
        return "it was read to the end and draws its line outside what the quantity it cuts ever"
                + " holds, about `" + position + "`";
    }

    /** {@code P} holds nothing above five, so the line at ten is above all of it. */
    @Test
    void aCaseHeldBelowTheLineIsSaidToBeOutsideItAndTheOtherKeepsItsBorder() {
        String said = report(atTen("    invariant deadline <= 5"));

        assertTrue(said.contains(outsideAt("r@P.deadline")), said);
        assertTrue(said.contains("read as f/r@Q.deadline: = 11"), said);
        assertTrue(said.contains("read as f/r@Q.deadline: = 10"), said);
        assertFalse(said.contains("read as f/r@P.deadline: = 11"), said);
        assertFalse(said.contains(outsideAt("r@Q.deadline")), said);
    }

    /** {@code P} holds nothing below twenty, so the line at ten is below all of it. */
    @Test
    void andACaseHeldAboveTheLine() {
        String said = report(atTen("    invariant deadline >= 20"));

        assertTrue(said.contains(outsideAt("r@P.deadline")), said);
        assertTrue(said.contains("read as f/r@Q.deadline: = 11"), said);
        assertFalse(said.contains("read as f/r@P.deadline: = 11"), said);
    }

    /** A case that holds values either side of the line is not outside it, and keeps its border. */
    @Test
    void aCaseHoldingBothSidesOfTheLineKeepsItsBorder() {
        String said = report(atTen("    invariant deadline <= 50"));

        assertFalse(said.contains("draws its line outside"), said);
        assertTrue(said.contains("read as f/r@P.deadline: = 11"), said);
        assertTrue(said.contains("read as f/r@Q.deadline: = 11"), said);
    }

    /**
     * Where neither case reaches the line, each is said to be outside it, at its own quantity. The
     * line is still one the field runs across — {@code P} below it and {@code Q} above it — so what is
     * said is about each case and not that the rule draws nothing on the field.
     */
    @Test
    void whereNeitherCaseReachesTheLineEachIsSaidToBeOutsideItOnItsOwn() {
        String said = report(guarded("    invariant deadline <= 5", "    invariant deadline >= 20",
                "r.deadline > 10", "P { deadline = 3 }"));

        assertTrue(said.contains(outsideAt("r@P.deadline")), said);
        assertTrue(said.contains(outsideAt("r@Q.deadline")), said);
        assertFalse(said.contains(outsideAt("r.deadline")), said);
        assertFalse(said.contains("read as f/r@P.deadline: = 11"), said);
        assertFalse(said.contains("read as f/r@Q.deadline: = 11"), said);
    }

    /** A value singled out that a case never holds is outside that case in the same words. */
    @Test
    void aValueSingledOutThatACaseNeverHoldsIsOutsideThatCase() {
        String said = report(guarded("    invariant deadline <= 5", "", "r.deadline == 50",
                "Q { deadline = 3 }"));

        assertTrue(said.contains(outsideAt("r@P.deadline")), said);
        assertTrue(said.contains("read as f/r@Q.deadline: = 50"), said);
        assertFalse(said.contains("read as f/r@P.deadline: = 50"), said);
    }

    /**
     * A line between the field and another position, which is drawn on neither of them alone, is
     * held to the same question at each case: {@code P}'s deadline less a number of at most one never
     * gets above ten.
     */
    @Test
    void aLineBetweenTheFieldAndAnotherPositionIsOutsideTheCaseThatNeverReachesIt() {
        String said = report(guarded("    invariant deadline <= 5", "", "r.deadline - s.n > 10",
                "Q { deadline = 3 }"));

        assertTrue(said.contains(outsideAt("r@P.deadline")), said);
        assertTrue(said.contains("read as f/r@Q.deadline: = s.n + 11"), said);
        assertFalse(said.contains("read as f/r@P.deadline: = s.n + 11"), said);
    }

    /**
     * A line the field itself never reaches is said about the field, as it always was, and not about
     * each case: the reading of the field settles it before anything is filed. Which words it is said
     * in is that reading's and not what this holds.
     */
    @Test
    void aLineTheFieldItselfNeverReachesIsStillSaidAboutTheField() {
        String said = report(atTen("").replace("deadline <= 100", "deadline <= 5"));

        assertTrue(said.contains("about `r.deadline`"), said);
        assertFalse(said.contains("about `r@P.deadline`"), said);
        assertFalse(said.contains("about `r@Q.deadline`"), said);
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(
                SourceRendering.namedByIdentity(compilation.texts()));
    }
}
