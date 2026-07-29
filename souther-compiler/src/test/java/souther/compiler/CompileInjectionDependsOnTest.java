package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code depends on} names what an implementation calls (spec 12.6). An injection target — a behavior
 * with a type but no {@code fn}, implemented from Java (spec 13.2) — has no implementation here, so
 * it cannot declare {@code depends on}: the behavior that calls or composes it carries the requirement
 * instead. A fn-bearing behavior keeps declaring the behaviors its body calls.
 */
class CompileInjectionDependsOnTest {

    @Test
    void anInjectionTargetCannotDeclareDependsOn() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data N = Int
                behavior bar : (n: N) -> N
                let bar (n) = n
                behavior foo : (n: N) -> N depends on bar
                """));
        assertTrue(e.getMessage().contains("injection target"), e.getMessage());
        assertTrue(e.getMessage().contains("depends on"), e.getMessage());
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
