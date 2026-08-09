package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A function has no external representation, so a type that carries one — however deeply — cannot
 * cross a boundary. Which positions those are is decided by what the position requires of a type,
 * not by where the grammar happens to admit a function type.
 */
class CompileFunctionBoundaryTest {

    private static Diagnostic diagnosticOf(String src) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        return e.diagnostic();
    }

    @Test
    void aBehaviorInputCannotCarryAFunction() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { v: Int }
                behavior run : (p: (Int) -> Bool) -> R
                """);
        assertEquals("type.a-parameter-carries-a-function", d.messageKey());
    }

    @Test
    void aBehaviorOutputCannotCarryAFunction() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { v: Int }
                behavior run : (r: R) -> (Int) -> Bool
                """);
        assertEquals("type.an-output-carries-a-function", d.messageKey());
    }

    @Test
    void aFunctionNestedInACollectionIsFoundAtTheBoundary() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { v: Int }
                behavior run : (m: Map<String, List<(Int) -> Bool>>) -> R
                """);
        assertEquals("type.a-parameter-carries-a-function", d.messageKey());
    }
}
