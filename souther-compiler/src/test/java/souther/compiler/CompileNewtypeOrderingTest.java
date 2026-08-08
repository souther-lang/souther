package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A single-value newtype over an ordered primitive is ordered — by the value it wraps (spec
 * §primitives, ADR-0047) — and the sort family reads it the same way the comparison operators do.
 * The two used to disagree: {@code Amount > limit} was accepted while
 * {@code sortBy((r) -> r.amount, invoices)} was rejected as a key with no ordering (issue #99). The
 * wrapper carries the ordering itself, so the generated class is {@code Comparable} and the
 * runtime's natural-order compare reaches it.
 */
class CompileNewtypeOrderingTest {

    @Test
    void sortByAKeyThatIsANewtypeOrdersByTheWrappedValue() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sortBy )

                data Amount = Int
                data Invoice = { id: String, amount: Amount }
                data In = { invoices: List<Invoice> }
                data Out = { ids: List<String> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    ids = List.map((r) -> r.id, sortBy((r) -> r.amount, i.invoices))
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("invoices", List.of(
                Map.of("id", "c", "amount", 30L),
                Map.of("id", "a", "amount", 10L),
                Map.of("id", "b", "amount", 20L))));
        Object out = Codecs.apply(loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);

        assertEquals(List.of("a", "b", "c"),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("ids"));
    }

    @Test
    void sortMaxAndMinOverAListOfNewtypes() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort, max, min )

                data Amount = Int
                data In = { amounts: List<Amount> }
                data Out = { sorted: List<Amount>, largest: Option<Amount>, smallest: Option<Amount> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    sorted = sort(i.amounts),
                    largest = max(i.amounts),
                    smallest = min(i.amounts)
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("amounts", List.of(30L, 10L, 20L)));
        Object out = Codecs.apply(loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(List.of(10L, 20L, 30L), m.get("sorted"));
        assertEquals(30L, m.get("largest"));
        assertEquals(10L, m.get("smallest"));
    }

    @Test
    void aNewtypeOverAnOrderedTypeThatIsNotIntSortsToo() throws Exception {
        // String, Decimal, Date and DateTime carry as Comparable objects, not as a `long`
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort )

                data ProductId = String
                data In = { ids: List<ProductId> }
                data Out = { sorted: List<ProductId> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.ids) }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("ids", List.of("gamma", "alpha", "beta")));
        Object out = Codecs.apply(loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);

        assertEquals(List.of("alpha", "beta", "gamma"),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("sorted"));
    }

    @Test
    void aNewtypeOverANewtypeIsOrderedThroughBoth() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort )

                data Level = Int
                data Grade = Level
                data In = { grades: List<Grade> }
                data Out = { sorted: List<Grade> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.grades) }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("grades", List.of(3L, 1L, 2L)));
        Object out = Codecs.apply(loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);

        assertEquals(List.of(1L, 2L, 3L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("sorted"));
    }

    @Test
    void theGeneratedClassCarriesTheOrderingForJavaToo() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo exposing ( Amount, Enabled )

                data Amount = Int
                data Enabled = Bool
                data Out = { v: Int }

                behavior run : (m: Amount) -> Out constructs Out

                let run (m) = Out { v = 1 }
                """), getClass().getClassLoader());

        assertTrue(Comparable.class.isAssignableFrom(loader.loadClass("demo.Amount")),
                "a newtype over an ordered primitive is Comparable on the Java side");
        assertFalse(Comparable.class.isAssignableFrom(loader.loadClass("demo.Enabled")),
                "Bool has no ordering, so the newtype over it has none either");
    }

    @Test
    void anImportedNewtypeIsOrderedInTheImportingModule() throws Exception {
        // the base is read through the symbol table, which a linked compile fills from the import
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module money exposing ( Amount )

                data Amount = Int
                """, """
                module demo

                import money ( Amount )
                import List ( sort )

                data In = { amounts: List<Amount> }
                data Out = { sorted: List<Amount> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.amounts) }
                """)), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("amounts", List.of(30L, 10L, 20L)));
        Object out = Codecs.apply(loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);

        assertEquals(List.of(10L, 20L, 30L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("sorted"));
    }

    @Test
    void aNewtypeThatIsAlsoASumCaseKeepsBothItsInterfaces() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort )

                data Settled = Int
                data Estimated = Int
                data Charge = Settled | Estimated
                data In = { amounts: List<Settled> }
                data Out = { sorted: List<Settled> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.amounts) }
                """), getClass().getClassLoader());

        Class<?> settled = loader.loadClass("demo.Settled");
        assertTrue(Comparable.class.isAssignableFrom(settled));
        assertTrue(loader.loadClass("demo.Charge").isAssignableFrom(settled),
                "it is still a case of its sum");

        // the field is declared at the case, not the sum, so `Settled` is read and written as the
        // newtype it is — the adjacent tag is what `Charge` adds where a value stands as a `Charge`
        Object in = Codecs.decoded(loader, "demo.In", Map.of("amounts", List.of(30L, 10L, 20L)));
        Object out = Codecs.apply(loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);
        assertEquals(List.of(10L, 20L, 30L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("sorted"));
    }

    @Test
    void aProductDataIsStillNotOrdered() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                import List ( sort )

                data Invoice = { id: String, amount: Int }
                data In = { invoices: List<Invoice> }
                data Out = { sorted: List<Invoice> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.invoices) }
                """));

        assertTrue(e.getMessage().contains("Invoice"), e.getMessage());
    }

    @Test
    void aNewtypeOverAnUnorderedTypeIsStillRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                import List ( sort )

                data Enabled = Bool
                data In = { flags: List<Enabled> }
                data Out = { sorted: List<Enabled> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.flags) }
                """));

        assertTrue(e.getMessage().contains("Enabled"), e.getMessage());
    }
}
