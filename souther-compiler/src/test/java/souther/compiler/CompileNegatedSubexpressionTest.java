package souther.compiler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

/**
 * A unary minus is an ordinary expression with a child, and every walk over a body has to descend
 * into it. One of them did not: the checker's own {@code forEachChild} listed the node kinds it knew
 * and ended in a {@code default} that did nothing, so a subexpression under {@code -} was invisible
 * to the nine passes that delegate their recursion to it — helper-parameter inference, the
 * constant-construction collection, the shadowing and invariant rejections.
 *
 * <p>What the author saw was that {@code -double(x)} demanded a type annotation on {@code double}
 * while {@code 0 - double(x)} did not.
 */
class CompileNegatedSubexpressionTest {

    private static String moduleWith(String body) {
        return """
                module m

                data N = Int

                let double (x) = x * 2

                behavior f : (n: N) -> N constructs N
                let f (n) = N { value = %s }
                """.formatted(body);
    }

    @Test
    void aHelperCallUnderAMinusStillFixesItsParameterTypes() {
        assertDoesNotThrow(() -> Compiler.compile(moduleWith("-double(n.value)")),
                "a call under `-` is a call site like any other");
    }

    /** The same call not under a minus, as the control. */
    @Test
    void aPlainHelperCallFixesItsParameterTypes() {
        assertDoesNotThrow(() -> Compiler.compile(moduleWith("double(n.value)")));
    }

    /** Deeper: the minus is not the only node between the body and the call. */
    @Test
    void aHelperCallUnderAMinusInsideAConditionalIsFound() {
        assertDoesNotThrow(() -> Compiler.compile(moduleWith(
                "if n.value > 0 then -double(n.value) else 0")));
    }
}
