package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

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
