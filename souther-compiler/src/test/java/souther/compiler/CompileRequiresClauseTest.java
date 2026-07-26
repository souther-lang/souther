package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.SourceContext;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A {@code requires} clause names injection targets (spec 12.6, 13.2). A name that is not one is
 * reported where it was written, saying which rule it broke — not left to the call site, where it
 * used to surface as an arbitrary JVM call (E1401), advice for a problem the author did not have
 * (issue #96).
 */
class CompileRequiresClauseTest {

    @Test
    void requiresNamingAnImplementedBehaviorIsReportedAtTheClause() {
        String src = """
                module demo
                data A = { x: Int }
                data R = { z: Int }

                behavior helper : (a: A) -> R
                    constructs R
                let helper (a) = R { z = a.x }

                behavior use : (a: A) -> R
                    requires helper
                let use (a, helper) = helper(a)
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1607", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("helper"), e.getMessage());
    }

    @Test
    void requiresNamingACompositionIsReportedWithoutAdvisingToRemoveALet() {
        // a `>->` composition is its own implementation and has no `let` to remove, so the advice has
        // to be the one that holds for every implementation: take the name out of `requires`
        String src = """
                module demo
                data A = { x: Int }
                data R = { z: Int }

                behavior one : (a: A) -> A
                    constructs A
                let one (a) = A { x = a.x }

                behavior two : (a: A) -> R
                    constructs R
                let two (a) = R { z = a.x }

                behavior chain = one >-> two

                behavior use : (a: A) -> R
                    requires chain
                let use (a, chain) = chain(a)
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1607", e.code(), e.getMessage());
        String hint = new HumanRenderer(false).render(e.diagnostic(),
                new SourceContext("demo.sou", src), Locale.ENGLISH);
        assertTrue(hint.contains("Remove `chain` from `requires`"), hint);
        assertFalse(hint.contains("`let`"), "a composition has no `let` to remove: " + hint);
    }

    @Test
    void requiresNamingAnUnknownBehaviorIsReportedAtTheClause() {
        String src = """
                module demo
                data A = { x: Int }
                data R = { z: Int }

                behavior use : (a: A) -> R
                    requires nosuch
                let use (a, nosuch) = nosuch(a)
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1607", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("nosuch"), e.getMessage());
    }

    @Test
    void requiresNamingAnImportedImplementedBehaviorIsReportedAtTheClause() {
        // an imported behavior with a `let` in its own module is an implementation, not an injection
        // target: it is composed with `>->`, not injected.
        String lib = """
                module demo.lib exposing ( A, R, price )
                data A = { x: Int }
                data R = { z: Int }
                behavior price : (a: A) -> R
                    constructs R
                let price (a) = R { z = a.x }
                """;
        String app = """
                module demo.app
                import demo.lib ( A, R, price )
                behavior use : (a: A) -> R
                    requires price
                let use (a, price) = price(a)
                """;
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(lib, app)));
        assertEquals("E1607", e.code(), e.getMessage());
    }

    @Test
    void anArbitraryCallWithNoRequiresClauseIsStillE1401() {
        String src = """
                module demo
                data A = { x: Int }
                data R = { z: Int }
                behavior use : (a: A) -> R
                    constructs R
                let use (a) = someJavaMethod(a)
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1401", e.code(), e.getMessage());
    }
}
