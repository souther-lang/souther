package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;

import java.util.List;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An expression nested deeper than the walks can recurse must be reported, not thrown. Every phase
 * here descends an expression by recursion, so a deep enough one exhausts the stack — and a
 * {@code StackOverflowError} is not a {@code CompileException}, so it passes straight through the
 * recovery boundary: the command line prints a stack trace, and the language server, which catches
 * {@code RuntimeException} to stay alive, does not catch this and exits.
 *
 * <p>Each case runs on a thread with a small, fixed stack. What counts as "too deep" otherwise
 * depends on the stack the test happens to run with, which makes the same source compile on one run
 * and overflow on the next; pinning the stack makes the boundary the same everywhere.
 */
class CompileDeepExpressionTest {

    /** Small enough that the depths below are past it on any platform, large enough for the
     *  phases that are not recursing over the expression. */
    private static final int STACK_BYTES = 256 * 1024;

    private static String moduleWith(String expr) {
        return """
                module m

                data N = Int

                behavior f : (n: N) -> N constructs N
                let f (n) = N { value = %s }
                """.formatted(expr);
    }

    @Test
    void deeplyNestedParenthesesAreReported() throws InterruptedException {
        String expr = "(".repeat(5000) + "1" + ")".repeat(5000);

        assertReportsDepth(() -> Compiler.compile(moduleWith(expr)));
    }

    @Test
    void aVeryLongOperatorChainIsReported() throws InterruptedException {
        String expr = "1 + ".repeat(20000) + "1";

        assertReportsDepth(() -> Compiler.compile(moduleWith(expr)));
    }

    /** A module set goes through the same walks, so it needs the same answer. */
    @Test
    void theSameHoldsForAModuleSet() throws InterruptedException {
        String expr = "(".repeat(5000) + "1" + ")".repeat(5000);

        assertReportsDepth(() -> Compiler.compileModules(List.of(moduleWith(expr))));
    }

    /** Runs {@code work} on a thread with {@link #STACK_BYTES} of stack and asserts it came back
     *  with a depth diagnostic rather than an {@code Error}. */
    private static void assertReportsDepth(Runnable work) throws InterruptedException {
        AtomicReference<Throwable> caught = new AtomicReference<>();
        Thread t = new Thread(null, () -> {
            try {
                work.run();
            } catch (Throwable x) {
                caught.set(x);
            }
        }, "deep-expression", STACK_BYTES);
        t.start();
        t.join();

        Throwable thrown = caught.get();
        assertNotNull(thrown, "a source this deep should not compile on a " + STACK_BYTES
                + "-byte stack; the test no longer exercises the depth boundary");
        assertInstanceOf(CompileException.class, thrown,
                "expected a diagnostic, got " + thrown.getClass().getName());
        assertTrue(thrown.getMessage().contains("deep"),
                "expected a depth diagnostic, got: " + thrown.getMessage());
    }
}
