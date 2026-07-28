package souther.compiler;

import net.unit8.raoh.Ok;
import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value of a type its module does not expose reaches another module through a field of a data
 * that module does expose. It arrives opaque: it may be held and handed back, and it may not be
 * opened. Reading a field of it, and comparing two of them, both read its representation, so both
 * are refused here rather than emitted as bytecode that fails with {@code IllegalAccessError}
 * (issue #187, the family of #124).
 */
class CompileOpaqueUnexposedValueTest {

    private static final String UP = """
            module up exposing ( Order, label )
            data UserId = String
            data Order = { by: UserId }
            behavior label : (id: UserId) -> String
            let label (id) = id.value
            """;

    @Test
    void suchAValueIsHeldAndHandedBackToItsOwnModule() throws Exception {
        // What the refusals above must not take away: the value arrives, sits in a field of this
        // module's own data, and goes back into a behavior of the module that owns the type. Run it,
        // because compiling is what the two refused cases also did.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of(UP, """
                module down exposing ( Out, read )
                import up ( Order, label )
                data Out = { by: up.Order, s: String }
                behavior read : (o: Order) -> Out
                    constructs Out
                let read (o) = Out { by = o, s = label(o.by) }
                """)), getClass().getClassLoader());

        Object order = ((Ok<?>) Codecs.decode(loader, "up.Order", Map.of("by", "abc"))).value();
        Object impl = loader.loadClass("down.Read$Impl").getConstructor().newInstance();
        Object out = impl.getClass().getMethod("apply", Object.class).invoke(impl, order);

        assertEquals("Out[by=Order[by=UserId[value=abc]], s=abc]", out.toString());
    }

    @Test
    void readingAFieldOfATypeItsModuleDoesNotExposeIsRefused() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, """
                        module down exposing ( Out, read )
                        import up ( Order )
                        data Out = { s: String }
                        behavior read : (o: Order) -> Out
                            constructs Out
                        let read (o) = Out { s = o.by.value }
                        """)));

        assertTrue(e.getMessage().contains("UserId"), e.getMessage());
        assertTrue(e.getMessage().contains("up"), e.getMessage());
    }

    @Test
    void comparingTwoValuesOfATypeItsModuleDoesNotExposeIsRefused() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, """
                        module down exposing ( Out, read )
                        import up ( Order )
                        data Out = { s: String }
                        behavior read : (o: Order) -> Out
                            constructs Out
                        let read (o) = Out { s = if o.by == o.by then "y" else "n" }
                        """)));

        assertTrue(e.getMessage().contains("UserId"), e.getMessage());
        assertTrue(e.getMessage().contains("up"), e.getMessage());
    }
}
