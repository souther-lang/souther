package souther.compiler;

import souther.compiler.diag.CompileException;

import souther.compiler.ast.Ast;
import souther.compiler.check.Lower;
import souther.compiler.check.Resolve;
import souther.compiler.check.TypeChecker;
import souther.compiler.codegen.Backend;
import souther.compiler.derive.Deriver;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Type variables {@code 'a} (ADR-0028) are written only in the shipped core. A non-recursive core
 * helper that carries one is monomorphised by inline expansion — the variable resolves to the
 * concrete argument type at each call site — so no polymorphic method is emitted. A user module may
 * not write a type variable at all; that is what keeps user models bounded.
 */
class CompileTypeVariableTest {

    /** Compiles a core (reserved-namespace) module directly, bypassing the user-facing guard. */
    private static Map<String, byte[]> compileCore(String src) {
        Ast.Module m = Deriver.derive(Resolve.module(CstFrontend.parse(src)));
        Ast.Module lowered = Lower.run(m);
        TypeChecker.Checked checked =
                TypeChecker.checkOrThrow(m, TypeChecker.symbols(m), Map.of(), Set.of(), lowered);
        return Backend.generate(lowered, checked);
    }

    @Test
    void aCoreGenericHelperMonomorphisesByInlining() throws Exception {
        // `identity` is written once with `'a`; the `Int` call site resolves it to Int on inlining.
        String core = """
                module souther.gen

                data In = { v: Int }
                data Out = { v: Int }

                behavior echo : (i: In) -> Out constructs Out

                let identity (x: 'a) = x
                let echo (i) = Out { v = identity(i.v) }
                """;
        BytesClassLoader loader = new BytesClassLoader(compileCore(core), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "souther.gen.In", Map.of("v", 7L));
        Object out = Codecs.apply(loader.loadClass("souther.gen.Echo" + "$Impl")
                .getConstructor().newInstance(), in);
        assertEquals(7L, ((Map<?, ?>) Codecs.encode(loader, "souther.gen.Out", out)).get("v"),
                "identity returns its argument unchanged");
    }

    @Test
    void aTypeVariableInAListPositionIsAllowedInTheCore() {
        String core = """
                module souther.gen
                let firstOr (xs: List<'a>, fallback: 'a) = fallback
                """;
        assertDoesNotThrow(() -> compileCore(core));
    }

    @Test
    void aUserModuleCannotWriteATypeVariable() {
        String user = """
                module demo
                data Out = { v: Int }
                behavior echo : (i: Out) -> Out constructs Out
                let identity (x: 'a) = x
                let echo (i) = i
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(user));
        assertEquals(true, e.getMessage().contains("type variable"), e.getMessage());
    }
}
