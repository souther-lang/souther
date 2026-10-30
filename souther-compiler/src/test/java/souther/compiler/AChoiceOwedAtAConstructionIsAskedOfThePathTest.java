package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An invariant clause written as a choice is established where the path leaves no run on which
 * neither half holds, and refused where it leaves no run on which one does.
 *
 * <p>Neither half is proved alone: a guard may state the choice the other way round, and a half
 * may be settled by what the other half's guard rules out. Nor is a half that folds to false a
 * reason to stop asking — the other half is still owed.
 */
class AChoiceOwedAtAConstructionIsAskedOfThePathTest {

    private static String model(String clause, String body) {
        return """
                module demo

                data P = { a: Int, b: Int }
                    invariant c = %s

                behavior f : (x: Int, y: Int) -> P
                    constructs P

                let f (x, y) =
                    %s
                """.formatted(clause, body);
    }

    private static String choice(String body) {
        return model("a < 3 || b == 0", body);
    }

    /** What the discharge check said: the warnings, or the refusal it stopped at. */
    private static List<String> judged(String model) {
        try {
            return Compiler.compileWithWarnings(model).warnings().stream()
                    .map(Diagnostic::code)
                    .filter(code -> code.startsWith("E20"))
                    .toList();
        } catch (CompileException refused) {
            return List.of(refused.getMessage().substring(0, 5));
        }
    }

    /** The sentence a refusal is said in. Which of the two it is says whether the value fails the
     * invariant alone or only under what the path knows. */
    private static String refusal(String model) {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileWithWarnings(model));
        return refused.getMessage();
    }

    private static final String ON_A_PATH = "on a reachable path";

    @Test
    void aValueThatFailsTheChoiceByItselfIsRefusedAsFailingAlone() {
        String said = refusal(choice("P { a = 5, b = 7 }"));
        assertTrue(said.startsWith("E2010"), said);
        assertTrue(!said.contains(ON_A_PATH), said);
    }

    @Test
    void aValueTheGuardsAloneMakeFailTheChoiceIsRefusedAsFailingOnThePath() {
        String said = refusal(choice(
                "if x > 5 && y > 5 then P { a = x, b = y } else P { a = 0, b = 0 }"));
        assertTrue(said.startsWith("E2010"), said);
        assertTrue(said.contains(ON_A_PATH), said);
    }

    @Test
    void aBoundDerivedForAProductOfBoundedFactorsEstablishesAChoiceOverIt() {
        assertEquals(List.of(), judged("""
                module demo

                data Small = Int
                    invariant value >= 0 && value <= 10

                data P = { a: Int, b: Int }
                    invariant c = a >= 0 || b == 0

                behavior f : (x: Small, y: Small, z: Int) -> P
                    constructs P

                let f (x, y, z) = P { a = x.value * y.value, b = z }
                """));
    }

    @Test
    void aBoundDerivedForAProductDoesNotEstablishWhatItDoesNotBound() {
        assertEquals(List.of("E2011"), judged("""
                module demo

                data Small = Int
                    invariant value >= 0 && value <= 10

                data P = { a: Int, b: Int }
                    invariant c = a >= 11 || b == 0

                behavior f : (x: Small, y: Small, z: Int) -> P
                    constructs P

                let f (x, y, z) = P { a = x.value * y.value, b = z }
                """));
    }

    @Test
    void aDeniedConjunctionIsAChoiceTheGuardEstablishes() {
        String clause = "Bool.not(a >= 3 && b /= 0)";
        assertEquals(List.of(), judged(model(clause,
                "if x < 3 then P { a = x, b = y } else P { a = 0, b = 0 }")));
        assertEquals(List.of(), judged(model(clause,
                "if y == 0 then P { a = x, b = y } else P { a = 0, b = 0 }")));
        assertEquals(List.of("E2011"), judged(model(clause, "P { a = x, b = y }")));
        assertEquals(List.of("E2010"), judged(model(clause, "P { a = 5, b = 7 }")));
    }

    @Test
    void aChoiceWithAConjunctionInsideIsEstablishedByEitherWayOfHoldingIt() {
        String clause = "a < 3 || (b == 0 && c == 0)";
        String body = "if %s then P { a = x, b = y, c = z } else P { a = 0, b = 0, c = 0 }";
        assertEquals(List.of(), judged(three(clause, body.formatted("x < 3"))));
        assertEquals(List.of(), judged(three(clause, body.formatted("y == 0 && z == 0"))));
        assertEquals(List.of("E2011"), judged(three(clause, body.formatted("y == 0"))));
    }

    @Test
    void aChoiceOfThreeIsEstablishedByAGuardOnAnyOne() {
        String clause = "a < 3 || b == 0 || c == 0";
        String body = "if %s then P { a = x, b = y, c = z } else P { a = 0, b = 0, c = 0 }";
        assertEquals(List.of(), judged(three(clause, body.formatted("z == 0"))));
        assertEquals(List.of(), judged(three(clause, body.formatted("z == 0 || x < 3"))));
        assertEquals(List.of("E2011"), judged(three(clause, body.formatted("x > 3"))));
    }

    @Test
    void aHalfThePathCannotReadLeavesTheOtherHalfToBeEstablished() {
        String clause = "a * a > 7 || b == 0";
        assertEquals(List.of(), judged(model(clause,
                "if y == 0 then P { a = x, b = y } else P { a = 0, b = 0 }")));
        assertEquals(List.of("E2011"), judged(model(clause, "P { a = x, b = 7 }")));
    }

    @Test
    void eachOfTwoChoicesIsAskedItsOwnQuestionAndOnlyTheOneUnsettledIsNamed() {
        String model = """
                module demo

                data P = { a: Int, b: Int }
                    invariant first = a < 3 || b == 0
                    invariant second = b < 5 || a == 0

                behavior f : (x: Int, y: Int) -> P
                    constructs P

                let f (x, y) =
                    if x < 3 then P { a = x, b = y } else P { a = 0, b = 0 }
                """;
        List<Diagnostic> warned = Compiler.compileWithWarnings(model).warnings().stream()
                .filter(d -> d.code().startsWith("E20")).toList();
        assertEquals(1, warned.size());
        assertEquals("second", warned.getFirst().values().get("unsettled"));
        assertEquals("first", warned.getFirst().values().get("settled"));
    }

    /** Many guards that are choices, none of which bears on the one owed, followed by the guard
     * that does. With few of them the guard that does establishes the clause; here the look
     * through them runs out first, and a look that ran out has not shown that no run fails it. */
    @Test
    void aLookThroughMoreChoicesThanItMayTakeEstablishesNothing() {
        StringBuilder params = new StringBuilder();
        StringBuilder guards = new StringBuilder();
        int many = 40;
        for (int i = 0; i < many; i++) {
            params.append(", p").append(i).append(": Int");
            guards.append("    guard p").append(i).append(" < 0 || p").append(i)
                    .append(" > 10 else P { a = 0, b = 0 }\n");
        }
        String model = """
                module demo

                data P = { a: Int, b: Int }
                    invariant c = a < 3 || b == 0

                behavior f : (x: Int, y: Int%s) -> P
                    constructs P

                let f (x, y%s) = {
                %s    if y == 0 || x < 3 then P { a = x, b = y } else P { a = 0, b = 0 }
                }
                """.formatted(params, names(many), guards);
        assertEquals(List.of("E2011"), judged(model));
    }

    private static String names(int guards) {
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < guards; i++) {
            out.append(", p").append(i);
        }
        return out.toString();
    }

    private static String three(String clause, String body) {
        return """
                module demo

                data P = { a: Int, b: Int, c: Int }
                    invariant k = %s

                behavior f : (x: Int, y: Int, z: Int) -> P
                    constructs P

                let f (x, y, z) =
                    %s
                """.formatted(clause, body);
    }

    @Test
    void aGuardOnTheLeftHalfEstablishesIt() {
        assertEquals(List.of(), judged(choice(
                "if x < 3 then P { a = x, b = y } else P { a = 0, b = 0 }")));
    }

    @Test
    void aGuardOnTheRightHalfEstablishesIt() {
        assertEquals(List.of(), judged(choice(
                "if y == 0 then P { a = x, b = y } else P { a = 0, b = 0 }")));
    }

    @Test
    void aGuardThatMakesBothHalvesTrueEstablishesIt() {
        assertEquals(List.of(), judged(choice(
                "if x < 3 && y == 0 then P { a = x, b = y } else P { a = 0, b = 0 }")));
    }

    @Test
    void theSameChoiceAsAGuardWithItsHalvesExchangedEstablishesIt() {
        assertEquals(List.of(), judged(choice(
                "if y == 0 || x < 3 then P { a = x, b = y } else P { a = 0, b = 0 }")));
    }

    @Test
    void theSameChoiceAsAGuardInTheOrderItWasWrittenEstablishesIt() {
        assertEquals(List.of(), judged(choice(
                "if x < 3 || y == 0 then P { a = x, b = y } else P { a = 0, b = 0 }")));
    }

    @Test
    void aChoiceWrittenAsAnIfEstablishedByAGuardOnEitherHalfIsEstablished() {
        String clause = "if a < 3 then true else b == 0";
        assertEquals(List.of(), judged(model(clause,
                "if x < 3 then P { a = x, b = y } else P { a = 0, b = 0 }")));
        assertEquals(List.of(), judged(model(clause,
                "if y == 0 then P { a = x, b = y } else P { a = 0, b = 0 }")));
    }

    @Test
    void aChoiceWrittenAsAnIfThatNothingEstablishesIsReported() {
        assertEquals(List.of("E2011"), judged(model("if a < 3 then true else b == 0",
                "P { a = x, b = y }")));
    }

    @Test
    void aHalfThatFoldsToFalseLeavesTheOtherOwed() {
        assertEquals(List.of("E2011"), judged(choice("P { a = x, b = 7 }")));
    }

    @Test
    void aHalfThatFoldsToFalseIsDischargedByAGuardOnTheOther() {
        assertEquals(List.of(), judged(choice(
                "if x < 3 then P { a = x, b = 7 } else P { a = 0, b = 0 }")));
    }

    @Test
    void aConstructionWhoseBothHalvesFoldToFalseIsRefused() {
        assertEquals(List.of("E2010"), judged(choice("P { a = 5, b = 7 }")));
    }

    @Test
    void aConstructionWhoseOneHalfFoldsToTrueIsEstablished() {
        assertEquals(List.of(), judged(choice("P { a = 5, b = 0 }")));
    }

    @Test
    void aChoiceNothingOnThePathSettlesIsReported() {
        assertEquals(List.of("E2011"), judged(choice("P { a = x, b = y }")));
    }

    @Test
    void aChoiceThatTheValuesAloneAlwaysSatisfyIsEstablished() {
        assertEquals(List.of(), judged(model("a < 3 || a >= 3", "P { a = x, b = y }")));
    }

    @Test
    void aGuardThatRulesOutBothHalvesRefusesTheConstruction() {
        assertEquals(List.of("E2010"), judged(choice(
                "if x > 5 && y > 5 then P { a = x, b = y } else P { a = 0, b = 0 }")));
    }

    @Test
    void aChoiceOutOfAnInputOfTheSameTypeIsEstablished() {
        assertEquals(List.of(), judged("""
                module demo

                data P = { a: Int, b: Int }
                    invariant c = a < 3 || b == 0

                behavior g : (p: P) -> P
                    constructs P

                let g (p) = P { a = p.a, b = p.b }
                """));
    }
}
