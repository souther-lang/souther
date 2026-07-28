package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A `constructs` clause names a type the way a type is named anywhere else, through its module when it
 * is another module's. A qualified construction reports itself as `up.Amount`, so that is what the
 * clause has to be able to say; before this it could only say the bare name an `import` brings in,
 * which left a qualified construction impossible to declare.
 */
class CompileQualifiedConstructsTest {

    private static final String UP = """
            module up exposing ( Amount )

            data Amount = Int invariant value >= 0
            """;

    private static Object run(String down, long n) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(
                Compiler.compileModules(List.of(UP, down)), CompileQualifiedConstructsTest.class.getClassLoader());
        Object b = loader.loadClass("down.Run$Impl").getConstructor().newInstance();
        return Codecs.apply(b, Codecs.decoded(loader, "down.In", Map.of("n", n)));
    }

    @Test
    void aQualifiedConstructionIsDeclaredThroughItsModule() throws Exception {
        Object out = run("""
                module down exposing ( In, Out, run )

                data In = { n: Int }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out, up.Amount

                let run (i) = Out { m = up.Amount(i.n).value }
                """, 4L);

        assertEquals(4L, out.getClass().getMethod("m").invoke(out));
    }

    @Test
    void theClauseMayNameThroughTheModuleWhileTheBodyUsesTheImportedName() throws Exception {
        // the clause names a type, and `up.Amount` and an imported `Amount` are the same type, so
        // which spelling each side uses is not something the check has an opinion about
        Object out = run("""
                module down exposing ( In, Out, run )
                import up ( Amount )

                data In = { n: Int }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out, up.Amount

                let run (i) = Out { m = Amount(i.n).value }
                """, 8L);

        assertEquals(8L, out.getClass().getMethod("m").invoke(out));
    }

    @Test
    void theClauseMayNameBareWhileTheBodyQualifies() throws Exception {
        Object out = run("""
                module down exposing ( In, Out, run )
                import up ( Amount )

                data In = { n: Int }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out, Amount

                let run (i) = Out { m = up.Amount(i.n).value }
                """, 9L);

        assertEquals(9L, out.getClass().getMethod("m").invoke(out));
    }

    @Test
    void namingOneTypeTwiceIsADuplicateHoweverItIsSpelled() {
        String down = """
                module down exposing ( In, Out, run )
                import up ( Amount )

                data In = { n: Int }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out, Amount, up.Amount

                let run (i) = Out { m = Amount(i.n).value }
                """;

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, down)));

        assertTrue(e.getMessage().contains("constructs"), e.getMessage());
        assertTrue(e.getMessage().contains("Amount"), e.getMessage());
    }

    @Test
    void anInjectedBehaviorMayQualifyATypeItsOwnModuleDeclares() {
        // `Out` is exposed, so Java can build it. What answers that is the type, and the qualifier in
        // front of it does not change which type it is.
        String down = """
                module down exposing ( In, Out, lookup )

                data In = { n: Int }
                data Out = { m: Int }

                behavior lookup : (i: In) -> Out constructs down.Out
                """;

        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UP, down)));
    }

    @Test
    void anImportedNameIsStillDeclaredBare() throws Exception {
        Object out = run("""
                module down exposing ( In, Out, run )
                import up ( Amount )

                data In = { n: Int }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out, Amount

                let run (i) = Out { m = Amount(i.n).value }
                """, 6L);

        assertEquals(6L, out.getClass().getMethod("m").invoke(out));
    }
}
