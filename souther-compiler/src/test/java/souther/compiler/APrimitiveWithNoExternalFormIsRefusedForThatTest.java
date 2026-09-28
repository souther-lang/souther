package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code Rational} is a value a computation holds and no boundary writes (ADR-0116), so wherever
 * something crosses it is refused for having no external representation. It is not a name the
 * language declares of its own operations, and declaring one of the model's own would not give it a
 * representation, so the report says nothing of the kind.
 *
 * <p>Held for each position that asks: a behavior's parameter and its answer, at depth and as a
 * member of a union, and a data's field and a newtype's base. They are one question and have to
 * give one answer.
 */
class APrimitiveWithNoExternalFormIsRefusedForThatTest {

    private static void refused(String declarations) {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile("module demo\n\n" + declarations + "\n"));
        assertTrue(e.getMessage().contains("E1311"), e.getMessage());
        assertTrue(e.getMessage().contains("Rational"), e.getMessage());
        assertFalse(e.getMessage().contains("E1325"), e.getMessage());
        assertFalse(e.getMessage().contains("Declare this as a type of the model"), e.getMessage());
    }

    @Test
    void aParameterIsRefused() {
        refused("behavior f : (x: Rational) -> Int\nlet f (x) = 1");
    }

    @Test
    void anAnswerIsRefused() {
        refused("behavior f : (n: Int) -> Rational\nlet f (n) = 1 / 2");
    }

    @Test
    void anElementOfACollectionIsRefused() {
        refused("behavior f : (n: Int) -> List<Rational>\nlet f (n) = []");
    }

    @Test
    void aMemberOfAnAnswerIsRefused() {
        refused("behavior f : (n: Int) -> Int | Rational\nlet f (n) = n");
    }

    @Test
    void aFieldIsRefused() {
        refused("data Ratio = { r: Rational }");
    }

    @Test
    void aNewtypeBaseIsRefused() {
        refused("data Ratio = Rational");
    }
}
