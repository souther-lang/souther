package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A program the compiler rejects must be rejected with a diagnostic. Anything else — an
 * IndexOutOfBounds, a ClassCast, a StackOverflow — is not a {@code CompileException}, so it escapes
 * the recovery boundary in {@code TypeChecker.checkModule} and reaches the author as a stack
 * trace; in the language server, where a non-diagnostic failure is swallowed so the server survives,
 * it reaches them as no marker at all.
 *
 * <p>These cases were found by mutating the example sources and compiling each mutation.
 */
class CompileBrokenInputIsDiagnosedTest {

    /** A sum that lists itself has no leaves to dispatch over, and every walk of its cases — codec
     * derivation, exhaustiveness, routing — would recurse forever. */
    @Test
    void aSumThatContainsItselfIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m

                data A = Int
                data S = S | A
                """));

        assertTrue(e.getMessage().contains("`S`"),
                "expected the cycle to name the sum, got: " + e.getMessage());
    }

    /** The same, one step removed: two sums that list each other. */
    @Test
    void twoSumsThatContainEachOtherAreRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m

                data A = Int
                data S = T | A
                data T = S | A
                """));

        assertTrue(e.getMessage().contains("`S`") || e.getMessage().contains("`T`"),
                "expected the cycle to name a sum, got: " + e.getMessage());
    }

    /** An example fixture of a shape the parameter's decoder cannot read: the decoder is generated
     * for the declared type and casts, so a fixture of another kind fails inside it. */
    @Test
    void anExampleFixtureOfTheWrongShapeIsAFixtureError() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m

                data Code = String
                data Item = { name: String }

                behavior g : (i: Item) -> Item
                let g (i) = i

                example g
                    | "a fixture of the wrong shape" :
                        (Code("x")) -> Item { name = "y" }
                """));

        assertTrue(e.getMessage().contains("E1812"),
                "the row's value is not of the position's type, said as code: " + e.getMessage());
        assertTrue(e.getMessage().contains("Item") && e.getMessage().contains("Code"),
                e.getMessage());
    }
}
