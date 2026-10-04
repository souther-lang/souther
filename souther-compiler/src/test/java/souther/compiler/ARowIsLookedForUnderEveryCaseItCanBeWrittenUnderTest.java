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
 * A row for a decision rule reached through a name every case of a sum spreads is looked for under
 * every case the row can be, and its values are chosen under that case's own rules.
 *
 * <p>Which case a row is written under decides which rules its value is held to, so it is part of
 * what is searched for and not a choice made before the search. Each model here is asked with its
 * cases declared both ways round, and the answer is the same: the order a sum lists its cases in is
 * not something a rule depends on.
 */
class ARowIsLookedForUnderEveryCaseItCanBeWrittenUnderTest {

    private static final String NO_ROW_TAKES = "! no row takes a decision rule";

    private static final String NOTHING_COULD_SHOW = "nothing could show a row can be written";

    /**
     * {@code P} holds its deadline to five and {@code Q} holds nothing more, so a deadline above ten
     * is one only a {@code Q} has.
     */
    private static String aboveTen(String cases) {
        return """
                module probe.r exposing ( C, R, P, Q, f )

                data C = { deadline: Int }
                    invariant deadline >= 0 && deadline <= 100

                data P = { ...C }
                    invariant deadline <= 5

                data Q = { ...C }

                data R = %s

                behavior f : (r: R) -> Int

                let f (r) = if r.deadline > 10 then 1 else 0

                example f
                    | "one" : (Q { deadline = 3 }) -> 0
                """.formatted(cases);
    }

    /**
     * {@code P} relates its two fields and {@code Q} does not. Both above sixty is a row only a
     * {@code Q} can be, and the first above sixty with the second not is one a {@code P} can be as
     * well, with its second field low enough that the two add up to no more than a hundred.
     */
    private static String related(String cases) {
        return """
                module probe.r exposing ( C, R, P, Q, f )

                data C = { a: Int, b: Int }
                    invariant a >= 0 && a <= 100 && b >= 0 && b <= 100

                data P = { ...C }
                    invariant a + b <= 100

                data Q = { ...C }

                data R = %s

                behavior f : (r: R) -> Int

                let f (r) = if r.a > 60 then (if r.b > 60 then 2 else 1) else 0

                example f
                    | "one" : (Q { a = 3, b = 3 }) -> 0
                """.formatted(cases);
    }

    /**
     * A name spread through two sums: {@code R}'s cases spread it, and so do {@code P}'s. Only
     * {@code P2} holds a deadline above ten, which is two cases down.
     */
    private static String twoSumsDown(String inner, String outer) {
        return """
                module probe.r exposing ( C, R, P, P1, P2, Q, f )

                data C = { deadline: Int }
                    invariant deadline >= 0 && deadline <= 100

                data P1 = { ...C }
                    invariant deadline <= 5

                data P2 = { ...C }
                    invariant deadline >= 50

                data P = %s

                data Q = { ...C }
                    invariant deadline <= 5

                data R = %s

                behavior f : (r: R) -> Int

                let f (r) = if r.deadline > 10 then 1 else 0

                example f
                    | "one" : (Q { deadline = 3 }) -> 0
                """.formatted(inner, outer);
    }

    @Test
    void aRuleOnlyTheLaterCaseTakesIsShownWritableWhicheverCaseIsDeclaredFirst() {
        for (String cases : new String[] {"P | Q", "Q | P"}) {
            String said = report(aboveTen(cases));

            assertEquals(1, count(said, NO_ROW_TAKES), cases + "\n" + said);
            assertFalse(said.contains(NOTHING_COULD_SHOW), cases + "\n" + said);
        }
    }

    /**
     * The value is chosen under the case's own rules and not the sum's. Chosen under the sum, the
     * first field above sixty is one the second field's run says nothing against, and a {@code P}
     * written with both above sixty is refused.
     */
    @Test
    void aRuleIsHeldToTheRelationOfTheCaseItIsWrittenUnder() {
        for (String cases : new String[] {"P | Q", "Q | P"}) {
            String said = report(related(cases));

            assertEquals(2, count(said, NO_ROW_TAKES), cases + "\n" + said);
            assertFalse(said.contains(NOTHING_COULD_SHOW), cases + "\n" + said);
        }
    }

    @Test
    void aNameTwoSumsDownIsLookedForUnderEveryPairOfCases() {
        for (String inner : new String[] {"P1 | P2", "P2 | P1"}) {
            for (String outer : new String[] {"P | Q", "Q | P"}) {
                String said = report(twoSumsDown(inner, outer));

                assertEquals(1, count(said, NO_ROW_TAKES), inner + " / " + outer + "\n" + said);
                assertFalse(said.contains(NOTHING_COULD_SHOW), inner + " / " + outer + "\n" + said);
            }
        }
    }

    /**
     * Where no case holds a deadline above ten, every way of writing the row was shown to leave
     * nothing, and that is the model's answer about the rule rather than a search that gave up.
     */
    @Test
    void whereEveryCaseLeavesTheRuleNothingTheRulesAreSaidToLeaveNothing() {
        for (String cases : new String[] {"P | Q", "Q | P"}) {
            String said = report(aboveTen(cases).replace("data Q = { ...C }",
                    "data Q = { ...C }\n    invariant deadline <= 8"));

            assertTrue(said.contains("no row is owed at 1 decision rule — the rules leave no value"
                    + " at a rule of the decision"), cases + "\n" + said);
            assertFalse(said.contains(NOTHING_COULD_SHOW), cases + "\n" + said);
        }
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
