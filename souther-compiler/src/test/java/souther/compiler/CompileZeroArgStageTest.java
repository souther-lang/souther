package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Spec 14.1: every stage after the first takes exactly one input, and a behavior that takes none is
 * no more composable than one that takes two. It reaches signature building before
 * {@code checkStagesAreSingleInput} has reported it, so the arity is confirmed where the routing
 * reads the input — otherwise the routing indexes an empty input list and the compile aborts with
 * an {@code IndexOutOfBoundsException} instead of a diagnostic.
 */
class CompileZeroArgStageTest {

    private static final String ZERO_ARG_SECOND_STAGE = """
            module m

            data D = Int

            behavior now : () -> D constructs D
            let now = D { value = 1 }

            behavior inc : (d: D) -> D constructs D
            let inc (d) = D { value = d.value + 1 }

            behavior p = inc >-> now
            """;

    @Test
    void aZeroInputBehaviorCannotFollowAnArrow() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(ZERO_ARG_SECOND_STAGE));

        assertTrue(e.getMessage().contains("`now` takes 0 inputs"),
                "expected the single-input rule, got: " + e.getMessage());
    }
}
