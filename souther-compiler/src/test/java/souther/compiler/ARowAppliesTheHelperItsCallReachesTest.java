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

    /** An intrinsic is applied under the name the call reaches, so an import that lets it be written
     * without its qualifier reaches the same kernel (#680). A table keyed by reach names misses on the
     * bare spelling, and a miss here reads as a row naming a construction it cannot make. The row
     * holding is what says the kernel ran: a value it did not answer would be E1903 or E1905. */
    @Test
    void aLibraryIntrinsicWrittenBareIsAppliedUnderTheNameItReaches() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                import String ( length )
                data In  = { s: String }
                data Out = { n: Int }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { n = String.length(i.s) }
                example go
                    | "bare" : (In { s = "abc" }) -> Out { n = length("abc") }
                """));
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
     * A binding that shares a helper's spelling is the binding: the row's expectation is compiled as
     * this module's code, so its {@code twice} is the lambda the row bound and not the helper. The
     * mismatch's own content is what proves it — the expectation computed 103, the binding's answer,
     * where a lookup by spelling would have run the helper, got the 6 the behavior also returns, and
     * passed a row that states something else.
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
        assertEquals("E1905", e.diagnostic().code(), e.getMessage());
        assertTrue(e.getMessage().contains("103"),
                "the expectation is the binding's answer, not the helper's: " + e.getMessage());
    }
}
