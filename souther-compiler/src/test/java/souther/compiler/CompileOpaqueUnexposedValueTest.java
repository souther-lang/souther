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

    /** A hidden newtype behind an exposed one, a hidden data, and collections of hidden values. */
    private static final String KINDS = """
            module up exposing ( Wrap, Holder )
            data Inner = String
            data Wrap = Inner
            data Hidden = { n: Int }
            data Ident = String
            data Holder = { w: Wrap, h: Hidden, ids: List<Ident>, tags: Set<Ident>, named: Map<String, Ident> }
            """;

    private static String comparing(String body) {
        return """
                module down exposing ( Out, same )
                import up ( Holder )
                data Out = { b: Bool }
                behavior same : (a: Holder, b: Holder) -> Out
                    constructs Out
                let same (a, b) = Out { b = %s }
                """.formatted(body);
    }

    private static Object runComparing(String body) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(
                Compiler.compileModules(List.of(KINDS, comparing(body))), CompileOpaqueUnexposedValueTest.class.getClassLoader());
        Object h = ((Ok<?>) Codecs.decode(loader, "up.Holder", Map.of(
                "w", "a", "h", Map.of("n", 1L), "ids", List.of("a"),
                "tags", List.of("a"), "named", Map.of("k", "a")))).value();
        Object impl = loader.loadClass("down.Same$Impl").getConstructor().newInstance();
        return impl.getClass().getMethod("apply", Object.class, Object.class).invoke(impl, h, h);
    }

    @Test
    void comparingThroughANewtypeChainWhoseInnerIsNotExposedIsRefused() {
        // `Wrap` is exposed and wraps `Inner`, which is not. Comparison opens a newtype to the value
        // it wraps and keeps going, so it reaches `Inner` and names a class out of reach here.
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(KINDS, comparing("a.w == b.w"))));

        assertTrue(e.getMessage().contains("Inner"), e.getMessage());
    }

    @Test
    void orderingThroughSuchAChainIsRefusedToo() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(KINDS, comparing("a.w < b.w"))));

        assertTrue(e.getMessage().contains("Inner"), e.getMessage());
    }

    @Test
    void comparingADataItsModuleDoesNotExposeIsAllowed() throws Exception {
        // A data is compared by its fields, by the module that declares it — nothing is opened here,
        // so this compares wherever the value arrives. Haskell and Elm settle it the same way.
        assertEquals("Out[b=true]", runComparing("a.h == b.h").toString());
    }

    @Test
    void comparingCollectionsOfSuchValuesIsAllowed() throws Exception {
        assertEquals("Out[b=true]", runComparing("a.ids == b.ids").toString());
        assertEquals("Out[b=true]", runComparing("a.tags == b.tags").toString());
        assertEquals("Out[b=true]", runComparing("a.named == b.named").toString());
    }

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
