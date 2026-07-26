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
 * The two used to disagree: {@code 金額 > 基準} was accepted while {@code sortBy((r) -> r.金額, …)}
 * was rejected as a key with no ordering (issue #99). The wrapper carries the ordering itself, so
 * the generated class is {@code Comparable} and the runtime's natural-order compare reaches it.
 */
class CompileNewtypeOrderingTest {

    @Test
    void sortByAKeyThatIsANewtypeOrdersByTheWrappedValue() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sortBy )

                data 金額 = Int
                data 請求 = { id: String, 額: 金額 }
                data In = { 請求: List<請求> }
                data Out = { ids: List<String> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { ids = List.map((r) -> r.id, sortBy((r) -> r.額, i.請求)) }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("請求", List.of(
                Map.of("id", "c", "額", 30L),
                Map.of("id", "a", "額", 10L),
                Map.of("id", "b", "額", 20L))));
        Object out = Codecs.apply(loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);

        assertEquals(List.of("a", "b", "c"),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("ids"));
    }

    @Test
    void sortMaxAndMinOverAListOfNewtypes() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort, max, min )

                data 金額 = Int
                data In = { 額: List<金額> }
                data Out = { sorted: List<金額>, 最大: Option<金額>, 最小: Option<金額> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.額), 最大 = max(i.額), 最小 = min(i.額) }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("額", List.of(30L, 10L, 20L)));
        Object out = Codecs.apply(loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(List.of(10L, 20L, 30L), m.get("sorted"));
        assertEquals(30L, m.get("最大"));
        assertEquals(10L, m.get("最小"));
    }

    @Test
    void aNewtypeOverAnOrderedTypeThatIsNotIntSortsToo() throws Exception {
        // String, Decimal, Date and DateTime carry as Comparable objects, not as a `long`
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort )

                data 商品ID = String
                data In = { ids: List<商品ID> }
                data Out = { sorted: List<商品ID> }

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

                data レベル = Int
                data 管理職 = レベル
                data In = { ranks: List<管理職> }
                data Out = { sorted: List<管理職> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.ranks) }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("ranks", List.of(3L, 1L, 2L)));
        Object out = Codecs.apply(loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);

        assertEquals(List.of(1L, 2L, 3L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("sorted"));
    }

    @Test
    void theGeneratedClassCarriesTheOrderingForJavaToo() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo exposing ( 金額, 有効 )

                data 金額 = Int
                data 有効 = Bool
                data Out = { v: Int }

                behavior run : (m: 金額) -> Out constructs Out

                let run (m) = Out { v = 1 }
                """), getClass().getClassLoader());

        assertTrue(Comparable.class.isAssignableFrom(loader.loadClass("demo.金額")),
                "a newtype over an ordered primitive is Comparable on the Java side");
        assertFalse(Comparable.class.isAssignableFrom(loader.loadClass("demo.有効")),
                "Bool has no ordering, so the newtype over it has none either");
    }

    @Test
    void anImportedNewtypeIsOrderedInTheImportingModule() throws Exception {
        // the base is read through the symbol table, which a linked compile fills from the import
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module money exposing ( 金額 )

                data 金額 = Int
                """, """
                module demo

                import money ( 金額 )
                import List ( sort )

                data In = { 額: List<金額> }
                data Out = { sorted: List<金額> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.額) }
                """)), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("額", List.of(30L, 10L, 20L)));
        Object out = Codecs.apply(loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);

        assertEquals(List.of(10L, 20L, 30L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("sorted"));
    }

    @Test
    void aNewtypeThatIsAlsoASumCaseKeepsBothItsInterfaces() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( sort )

                data 確定額 = Int
                data 見積額 = Int
                data 金額 = 確定額 | 見積額
                data In = { 額: List<確定額> }
                data Out = { sorted: List<確定額> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.額) }
                """), getClass().getClassLoader());

        Class<?> 確定額 = loader.loadClass("demo.確定額");
        assertTrue(Comparable.class.isAssignableFrom(確定額));
        assertTrue(loader.loadClass("demo.金額").isAssignableFrom(確定額),
                "it is still a case of its sum");

        // a newtype case of a sum is adjacently tagged, so its fixture carries `type` and `value`
        Object in = Codecs.decoded(loader, "demo.In", Map.of("額", List.of(
                Map.of("type", "確定額", "value", 30L),
                Map.of("type", "確定額", "value", 10L),
                Map.of("type", "確定額", "value", 20L))));
        Object out = Codecs.apply(loader.loadClass("demo.Run$Impl").getConstructor().newInstance(), in);
        // the field is declared at the case, not the sum, so the tag is not written back out
        assertEquals(List.of(Map.of("value", 10L), Map.of("value", 20L), Map.of("value", 30L)),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("sorted"));
    }

    @Test
    void aProductDataIsStillNotOrdered() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                import List ( sort )

                data 請求 = { id: String, 額: Int }
                data In = { 請求: List<請求> }
                data Out = { sorted: List<請求> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.請求) }
                """));

        assertTrue(e.getMessage().contains("請求"), e.getMessage());
    }

    @Test
    void aNewtypeOverAnUnorderedTypeIsStillRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                import List ( sort )

                data 有効 = Bool
                data In = { flags: List<有効> }
                data Out = { sorted: List<有効> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { sorted = sort(i.flags) }
                """));

        assertTrue(e.getMessage().contains("有効"), e.getMessage());
    }
}
