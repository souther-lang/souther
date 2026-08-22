package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * {@code depends on} names what an implementation calls (spec §depends-on), and what may be named is
 * a behavior whose requirement set is not empty. A behavior with a {@code let} and no clause of its
 * own requires nothing, so it is called by name rather than injected, and naming it is refused where
 * the clause is written. A fn-bearing behavior keeps declaring the behaviors its body calls.
 */
class CompileInjectionDependsOnTest {

    @Test
    void aBehaviorThatRequiresNothingIsNotNamedInDependsOn() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data N = Int
                behavior bar : (n: N) -> N
                let bar (n) = n
                behavior foo : (n: N) -> N depends on bar
                """));
        assertEquals("E1607", e.code(), e.getMessage());
    }

    @Test
    void aFnBehaviorStillDeclaresWhatItCalls() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                data N = Int
                behavior bar : (n: N) -> N
                behavior foo : (n: N) -> N depends on bar
                let foo (n, bar) = bar(n)
                """));
    }
}
