package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the compiler reads as a constant stops where the operator stops.
 *
 * <p>`&&` and `||` settle on their left operand, so `false && x` is `false` whatever `x` is — the
 * value of `x` is not part of the answer and its being unreadable here does not make the answer
 * unreadable. Read eagerly, a right operand this cannot fold takes a settled condition down with it,
 * and a construction whose argument the language says is a known constant goes uncheckedto run time.
 *
 * <p>Which is a recogniser being incomplete rather than wrong: what it declines to fold it declines
 * to claim anything about. It is still worth holding to the same rule as the emitter, because the two
 * answering differently about one expression is what makes a constant check depend on how the
 * constant was written.
 */
class AConstantConditionStopsWhereTheOperatorDoesTest {

    /** An arithmetic overflow is the shape this reads nothing out of. */
    private static final String UNFOLDABLE = "(9223372036854775807 + 1 == 0)";

    private static String source(String written) {
        return """
                module demo
                data F = Bool
                    invariant holds = value == true
                behavior make : (n: Int) -> F constructs F
                let make (n) = F(%s)
                """.formatted(written);
    }

    /** A conjunction settled false is a constant the invariant refuses, and it is refused here. */
    @Test
    void aConjunctionSettledByItsLeftIsStillAConstant() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(source("false && " + UNFOLDABLE)));

        assertTrue(e.getMessage().contains("holds"), e.getMessage());
    }

    /** And a disjunction settled true is one it admits, so nothing is reported. */
    @Test
    void aDisjunctionSettledByItsLeftIsStillAConstant() {
        assertDoesNotThrow(() -> Compiler.compile(source("true || " + UNFOLDABLE)));
    }

    /** Where the left operand does not settle it, the right one is read as ever. */
    @Test
    void anUnsettledConditionStillReadsItsRight() {
        assertThrows(CompileException.class, () -> Compiler.compile(source("true && false")));
        assertDoesNotThrow(() -> Compiler.compile(source("false || true")));
    }
}
