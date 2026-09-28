package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An anonymous union appears only in a behavior's output; a parameter type is always a single named type, a
 * named sum included (spec §union-intersection, §unmarked-output). Writing {@code (x: A | B)} in a parameter
 * is rejected — declare {@code data AB = A | B} and take {@code (x: AB)}, opening it with {@code match},
 * which {@link CompileUnionParamTest} compiles and runs.
 */
class CompileUnionParamRejectTest {

    @Test
    void anAnonymousUnionParameterIsRejected() {
        String src = """
                module demo
                data Sub = Int
                data Pre = Int
                data Done = Int
                behavior finish : (app: Sub | Pre) -> Done constructs Done
                let finish (app) = match app with
                    | Sub as s -> Done { value = s.value }
                    | Pre as p -> Done { value = p.value }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertTrue(e.getMessage().contains("app"), e.getMessage());
    }
}
