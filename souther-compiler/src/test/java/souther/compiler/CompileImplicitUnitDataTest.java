package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A case name written where a module introduces a type — a sum's case list, a behavior's output —
 * needs no separate {@code data} declaration when it carries no fields: the name alone declares the
 * unit (spec 8.4). Before this, {@code data Terms = Net15 | Net30} demanded a {@code data Net15}
 * line that repeated the name and said nothing else.
 *
 * <p>Everywhere else a type is referred to rather than introduced, and an unknown name there is
 * still unknown.
 */
class CompileImplicitUnitDataTest {

    private BytesClassLoader loader(String source) {
        return new BytesClassLoader(Compiler.compile(source), getClass().getClassLoader());
    }

    @Test
    void anUndeclaredCaseOfASumIsAUnitData() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data Terms = Net15 | Net30 | EndOfNextMonth
                """);

        Object v = Codecs.decoded(loader, "demo.Terms", "Net30");   // an enumeration is its name
        assertInstanceOf(loader.loadClass("demo.Net30"), v);
    }

    @Test
    void anUndeclaredCaseOfABehaviorOutputIsAUnitData() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data Cart = { n: Int }
                data Priced = { total: Int }

                behavior quote : (c: Cart) -> Priced | EmptyCart
                    constructs Priced, EmptyCart

                let quote (c) = {
                    require c.n >= 1 else EmptyCart
                    Priced { total = c.n }
                }
                """);

        Object cart = Codecs.decoded(loader, "demo.Cart", Map.of("n", 0L));
        Object behavior = loader.loadClass("demo.Quote$Impl").getConstructor().newInstance();
        Object out = behavior.getClass().getMethod("apply", Object.class).invoke(behavior, cart);

        assertInstanceOf(loader.loadClass("demo.EmptyCart"), out);
    }

    /** A single output type is an output all the same: a behavior whose result carries nothing
     * declares that result by naming it. */
    @Test
    void anUndeclaredSingleOutputTypeIsAUnitData() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data Cart = { n: Int }

                behavior close : (c: Cart) -> Closed constructs Closed
                let close (c) = Closed
                """);

        Object cart = Codecs.decoded(loader, "demo.Cart", Map.of("n", 1L));
        Object behavior = loader.loadClass("demo.Close$Impl").getConstructor().newInstance();
        Object out = behavior.getClass().getMethod("apply", Object.class).invoke(behavior, cart);

        assertInstanceOf(loader.loadClass("demo.Closed"), out);
    }

    /** A composition produces what its stages produce, so a name only it declares is a case nothing
     * can return. Reading it as a unit is what lets the mismatch be reported (E1604) rather than the
     * name being called unknown. */
    @Test
    void aCaseOnlyAnExposedCompositionNamesIsAMismatch() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo exposing ( process : Doubled | Refused )

                data Amount = Int
                data Doubled = Int

                behavior guard : (a: Amount) -> Amount
                let guard (a) = a

                behavior toDoubled : (a: Amount) -> Doubled constructs Doubled
                let toDoubled (a) = Doubled { value = a.value }

                behavior process = guard >-> toDoubled
                """));

        assertEquals("E1604", e.code());
    }

    @Test
    void anUndeclaredParameterTypeIsStillUnknown() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Out = { n: Int }

                behavior f : (c: Basket) -> Out constructs Out
                let f (c) = Out { n = 1 }
                """));

        assertTrue(e.getMessage().contains("Basket"), e.getMessage());
    }

    @Test
    void anUndeclaredNameInConstructsIsStillUnknown() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Cart = { n: Int }
                data Out = { n: Int }

                behavior f : (c: Cart) -> Out constructs Out, Refused
                let f (c) = Out { n = 1 }
                """));

        assertTrue(e.getMessage().contains("Refused"), e.getMessage());
    }

    /** A qualified name says which module declares it, so it is a reference wherever it is written. */
    @Test
    void anUnresolvedQualifiedOutputCaseIsStillUnknown() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module up exposing ( Amount )
                        data Amount = Int
                        """, """
                        module down
                        import up ( Amount )

                        data Out = { n: Int }

                        behavior f : (a: up.Amount) -> Out | up.Refused constructs Out
                        let f (a) = Out { n = a.value }
                        """)));

        assertTrue(e.getMessage().contains("Refused"), e.getMessage());
    }

    /** An imported name is declared — by the module it came from. Introducing one here would give a
     * second type of the same name, and the value would be of the wrong one. */
    @Test
    void anImportedUnitIsNotDeclaredAgainHere() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module up exposing ( Done )
                data Done
                """, """
                module down
                import up ( Done )

                data Cart = { n: Int }

                behavior finish : (c: Cart) -> Done constructs Done
                let finish (c) = Done
                """));

        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Object cart = Codecs.decoded(loader, "down.Cart", Map.of("n", 1L));
        Object behavior = loader.loadClass("down.Finish$Impl").getConstructor().newInstance();
        Object out = behavior.getClass().getMethod("apply", Object.class).invoke(behavior, cart);

        assertEquals("up.Done", out.getClass().getName());
    }
}
