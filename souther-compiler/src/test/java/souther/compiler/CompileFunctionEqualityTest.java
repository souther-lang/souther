package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Two functions are not equal or unequal: {@code ==} is value equality (ADR-0009), and a function
 * value has no value to compare. Refused where the comparison is written rather than left to
 * compare object identity at run time, and refused the same way where a {@code Set} or a
 * {@code Map} would ask the same question of an element or a key.
 */
class CompileFunctionEqualityTest {

    private static Diagnostic diagnosticOf(String src) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        return e.diagnostic();
    }

    @Test
    void twoFunctionsCannotBeCompared() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { same: Bool }
                behavior run : (n: Int) -> R
                    constructs R
                let run (n) = {
                    let p: (Int) -> Bool = (x) -> x > n
                    let q: (Int) -> Bool = (x) -> x > n
                    R { same = p == q }
                }
                """);
        assertEquals("check.equality.function", d.messageKey());
    }

    @Test
    void aSetCannotHoldFunctions() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { n: Int }
                behavior run : (n: Int) -> R
                    constructs R
                let run (n) = {
                    let p: (Int) -> Bool = (x) -> x > n
                    let s: Set<(Int) -> Bool> = Set.singleton(p)
                    R { n = Set.size(s) }
                }
                """);
        assertEquals("check.set.function", d.messageKey());
    }

    @Test
    void aMapCannotBeKeyedByAFunction() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { n: Int }
                behavior run : (n: Int) -> R
                    constructs R
                let run (n) = {
                    let p: (Int) -> Bool = (x) -> x > n
                    let m: Map<(Int) -> Bool, Int> = Map.singleton(p, 1)
                    R { n = Map.size(m) }
                }
                """);
        assertEquals("check.map.key.function", d.messageKey());
    }
}
