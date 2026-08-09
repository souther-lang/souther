package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/** Diagnostic codes for two rejected constructs: {@code null} (E1301) and a call to a name nothing
 *  declares (E1023). */
class CompileErrorCodeTest {

    @Test
    void nullIsE1301() {
        String src = """
                module demo
                data N = Int
                behavior f : (n: N) -> N constructs N
                let f (n) = null
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1301", e.code());
    }

    @Test
    void callingANameNothingDeclaresIsE1023() {
        String src = """
                module demo
                data N = Int
                behavior f : (n: N) -> N constructs N
                let f (n) = someJavaMethod(n)
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1023", e.code());
    }
}
