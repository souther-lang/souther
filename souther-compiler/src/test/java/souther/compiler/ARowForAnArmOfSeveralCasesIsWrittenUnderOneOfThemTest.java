package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row composed for an arm that leaves a value several cases is written under one of them, and so
 * takes the arm.
 *
 * <p>A row is one case. Composed against several at once, it is built as whatever the declaration
 * puts at the position, and the case built may be one the arm leaves out — a row that takes another
 * arm. Which arm that was turned on the order the cases are declared in, so every model here is
 * asked with the cases declared and listed in more than one order, and the answer is the same.
 */
class ARowForAnArmOfSeveralCasesIsWrittenUnderOneOfThemTest {

    private static final String NO_ROW_TAKES = "! no row takes a decision rule";

    private static final String NOTHING_COULD_SHOW = "nothing could show a row can be written";

    private static String matched(String cases, String arms) {
        return """
                module probe.r exposing ( Thing, A, B, C, D, Out, apply )

                data Thing = %s
                data Out = Int

                behavior apply : (x: Thing) -> Out
                    constructs Out

                let apply (x) =
                    match x with
                %s
                """.formatted(cases, arms);
    }

    @Test
    void anArmOfSeveralCasesIsComposedWhicheverCaseIsDeclaredFirst() {
        String[][] models = {
                {"A | B | C | D", "        | A -> Out(1)\n        | B | C | D -> Out(2)"},
                {"A | B | C | D", "        | A -> Out(1)\n        | D | C | B -> Out(2)"},
                {"A | B | C | D", "        | B -> Out(1)\n        | D | A | C -> Out(2)"},
                {"B | C | D | A", "        | A -> Out(1)\n        | B | C | D -> Out(2)"},
                {"A | B | C | D", "        | A | B -> Out(1)\n        | C | D -> Out(2)"},
        };
        for (String[] model : models) {
            String said = report(matched(model[0], model[1]));

            assertEquals(2, count(said, NO_ROW_TAKES), model[0] + "\n" + model[1] + "\n" + said);
            assertFalse(said.contains(NOTHING_COULD_SHOW), model[0] + "\n" + model[1] + "\n"
                    + said);
        }
    }

    /** An arm naming one case that is itself a sum leaves the value the leaves under it. */
    @Test
    void anArmOnACaseThatIsASumIsComposedUnderOneOfItsLeaves() {
        for (String cases : new String[] {"A | B", "B | A"}) {
            String said = report("""
                    module probe.r exposing ( Thing, A, B, B1, B2, Out, apply )

                    data B = B1 | B2
                    data Thing = %s
                    data Out = Int

                    behavior apply : (x: Thing) -> Out
                        constructs Out

                    let apply (x) =
                        match x with
                            | A -> Out(1)
                            | B -> Out(2)
                    """.formatted(cases));

            assertEquals(2, count(said, NO_ROW_TAKES), cases + "\n" + said);
            assertFalse(said.contains(NOTHING_COULD_SHOW), cases + "\n" + said);
        }
    }

    @Test
    void anArmOverAFieldIsComposedUnderOneOfItsCases() {
        String said = report("""
                module probe.r exposing ( Thing, A, B, C, Holder, Out, apply )

                data Thing = A | B | C
                data Holder = { r: Thing }
                data Out = Int

                behavior apply : (x: Holder) -> Out
                    constructs Out

                let apply (x) =
                    match x.r with
                        | A -> Out(1)
                        | B | C -> Out(2)
                """);

        assertEquals(2, count(said, NO_ROW_TAKES), said);
        assertFalse(said.contains(NOTHING_COULD_SHOW), said);
    }

    /** A comparison with a case is a choice of case, and the side it leaves several is such an
     *  arm. */
    @Test
    void theSideOfAComparisonWithACaseThatLeavesSeveralIsComposed() {
        for (String compared : new String[] {"x == A", "x /= A"}) {
            String said = report("""
                    module probe.r exposing ( Thing, A, B, C, Out, apply )

                    data Thing = A | B | C
                    data Out = Int

                    behavior apply : (x: Thing) -> Out
                        constructs Out

                    let apply (x) = if %s then Out(1) else Out(2)
                    """.formatted(compared));

            assertEquals(2, count(said, NO_ROW_TAKES), compared + "\n" + said);
            assertFalse(said.contains(NOTHING_COULD_SHOW), compared + "\n" + said);
        }
    }

    /**
     * {@code limited} holds its number to five and the others hold nothing more, so a number above
     * ten inside the arm is one only the arm's other case has.
     */
    private static String aboveTen(String limited, String arms) {
        return """
                module probe.r exposing ( K, Thing, A, B, C, apply )

                data K = { d: Int }
                    invariant d >= 0 && d <= 100
                data A = { ...K }
                data B = { ...K }%s
                data C = { ...K }%s
                data Thing = A | B | C

                behavior apply : (x: Thing) -> Int

                let apply (x) =
                    match x with
                        | A -> 1
                        | %s -> if x.d > 10 then 2 else 3
                """.formatted(
                limited.contains("B") ? "\n    invariant d <= 5" : "",
                limited.contains("C") ? "\n    invariant d <= 5" : "", arms);
    }

    /** One case of the arm leaves the rule nothing, and the row is written under the other. */
    @Test
    void aRuleOnlyOneCaseOfTheArmTakesIsComposedUnderThatCase() {
        for (String limited : new String[] {"B", "C"}) {
            for (String arm : new String[] {"B | C", "C | B"}) {
                String said = report(aboveTen(limited, arm));

                assertEquals(3, count(said, NO_ROW_TAKES), limited + " / " + arm + "\n" + said);
                assertFalse(said.contains(NOTHING_COULD_SHOW), limited + " / " + arm + "\n"
                        + said);
            }
        }
    }

    /** No case of the arm takes the rule, which is the model's answer about it. */
    @Test
    void whereNoCaseOfTheArmTakesTheRuleNoValueIsSaidToStandThere() {
        String said = report(aboveTen("BC", "B | C"));

        assertEquals(2, count(said, NO_ROW_TAKES), said);
        assertTrue(said.contains("no row is owed at 1 decision rule — no value can stand at a rule"
                + " of the decision"), said);
        assertFalse(said.contains(NOTHING_COULD_SHOW), said);
    }

    private static long count(String said, String line) {
        return said.lines().filter(each -> each.contains(line)).count();
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(
                SourceRendering.namedByIdentity(compilation.texts()));
    }
}
