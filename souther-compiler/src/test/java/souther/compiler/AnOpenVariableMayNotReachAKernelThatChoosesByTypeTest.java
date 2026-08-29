package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A kernel's lowering may read the type it is applied at — {@code List.sum} chooses between summing
 * {@code Int} and summing {@code Decimal} — so a call reaching one with a variable still open has
 * nothing for that choice to read.
 *
 * <p>It is refused where it is written, which is what lets a method emitted at a helper's own
 * declared signature be emitted once. The rule is the premise every emission of a polymorphic
 * helper rests on, so it is measured here rather than assumed: a change to it is a change to a test
 * and not a method that answers wrongly at run time.
 */
class AnOpenVariableMayNotReachAKernelThatChoosesByTypeTest {

    @Test
    void aHelperCannotCarryAnOpenVariableIntoAKernelThatChoosesByType() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Amount = Int

                let total (xs) = List.sum(xs)

                behavior billed : (a: Amount) -> Amount

                let billed (a) = a
                """));
        assertTrue(e.getMessage().contains("E1817"), e.getMessage());
    }
}
