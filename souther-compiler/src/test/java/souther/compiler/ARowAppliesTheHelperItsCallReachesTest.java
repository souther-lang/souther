package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fixture applies the helper its call reaches, not the one its spelling names.
 *
 * <p>An import lets a library name be written without its qualifier, and nothing rewrites that
 * spelling into the name the table of reached helpers is keyed by — the rewrite that does it for an
 * imported helper reads what the name denotes, and a library name denotes something else. So a row
 * applying one was looked up under the spelling the author wrote, missed, and was reported as naming
 * a construction it could not make (issue #397).
 */
class ARowAppliesTheHelperItsCallReachesTest {

    private static final String MODULE = """
            module demo
            import Int ( abs )
            data In  = { n: Int }
            data Out = { m: Int }
            behavior go : (i: In) -> Out constructs Out
            let go (i) = Out { m = Int.abs(i.n) }
            """;

    @Test
    void aRowMayApplyALibraryHelperWrittenBare() {
        assertDoesNotThrow(() -> Compiler.compile(MODULE + """
                example go
                    | "bare" : (In { n = -3 }) -> Out { m = abs(-3) }
                """));
    }

    @Test
    void theSameHelperWrittenQualifiedIsTheSameHelper() {
        assertDoesNotThrow(() -> Compiler.compile(MODULE + """
                example go
                    | "qualified" : (In { n = -3 }) -> Out { m = Int.abs(-3) }
                """));
    }

    /** The row is run rather than passed over: a fixture that applies the helper and states the wrong
     * answer fails as the mismatch it is. */
    @Test
    void aBareApplicationIsEvaluatedAndNotAssumed() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(MODULE + """
                example go
                    | "bare" : (In { n = -3 }) -> Out { m = abs(-4) }
                """));
        assertEquals("E1905", e.diagnostic().code(), e.getMessage());
    }

    /** Which library function a row applied decides what it is told about it, so that question is
     * asked with the name the call reaches too: an intrinsic has no method for a fixture to run, and
     * saying so is not the same as saying the call was not a construction. */
    @Test
    void aLibraryIntrinsicWrittenBareIsRefusedAsTheIntrinsicItIs() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                import String ( length )
                data In  = { s: String }
                data Out = { n: Int }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { n = String.length(i.s) }
                example go
                    | "bare" : (In { s = "abc" }) -> Out { n = length("abc") }
                """));
        assertTrue(e.getMessage().contains("a standard-library function is not one a fixture may apply"), e.getMessage());
    }

    /**
     * A helper another module publishes is applied the same way. It is reached under the module that
     * declares it, which is what the row is looked up with — and the row writes it bare, because the
     * import let it.
     */
    @Test
    void aRowMayApplyAHelperAnotherModulePublishes() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module up exposing ( twice )
                let twice (n: Int) : Int = n * 2
                """, """
                module down
                import up ( twice )
                data In  = { n: Int }
                data Out = { m: Int }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { m = twice(i.n) }
                example go
                    | "imported" : (In { n = 3 }) -> Out { m = twice(3) }
                """)));
    }

    /**
     * Which name a fixture looks a call up by is one question and whether it may look it up as a helper
     * at all is another. A binding that shares a helper's spelling is the binding, and a fixture cannot
     * apply what a binding holds — so the row is refused rather than answered by the helper.
     *
     * <p>The first row is what makes this reachable: it applies the helper, so the method is emitted and
     * a lookup by spelling would find one to run. Asked by spelling, the second row runs {@code twice}
     * over 3, gets the 6 the behavior also returns, and holds — a row that states one thing and is
     * passed by another.
     */
    @Test
    void aBindingIsNotTheHelperThatSharesItsSpelling() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data In  = { n: Int }
                data Out = { m: Int }
                let twice (n: Int) : Int = n * 2
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { m = twice(i.n) }
                example go
                    | "applies the helper" : (In { n = 1 }) -> Out { m = twice(1) }
                    | "shadow"             : (In { n = 3 }) -> {
                        let twice: (Int) -> Int = (k) -> k + 100
                        Out { m = twice(3) }
                      }
                """));
        assertEquals("E1903", e.diagnostic().code(), e.getMessage());
    }
}
