package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.Map;

import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** The Map building standard library ([#stdlib-map]): empty / singleton / insert / remove /
 *  isEmpty / size, over the immutable string-keyed Map. */
class CompileMapLibTest {

    @Test
    void buildAndQueryAMap() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Map ( singleton, insert, remove, isEmpty, size, containsKey )

                data In = { base: Map<String, Int> }
                data Out = {
                    built: Map<String, Int>
                    , one: Map<String, Int>
                    , afterRemove: Map<String, Int>
                    , n: Int
                    , baseEmpty: Bool
                    , builtEmpty: Bool
                    , hasB: Bool
                    , emptyMap: Map<String, Int>
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = {
                    let built = insert("b", 2, insert("a", 1, Map.empty))
                    Out {
                        built = built,
                        one = singleton("x", 9),
                        afterRemove = remove("a", i.base),
                        n = size(built),
                        baseEmpty = isEmpty(i.base),
                        builtEmpty = isEmpty(built),
                        hasB = containsKey("b", built),
                        emptyMap = Map.empty
                    }
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("base", Map.of("a", 1L, "c", 3L)));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(Map.of("a", 1L, "b", 2L), m.get("built"));
        assertEquals(Map.of("x", 9L), m.get("one"));
        assertEquals(Map.of("c", 3L), m.get("afterRemove"), "remove drops only the named key");
        assertEquals(2L, m.get("n"));
        assertEquals(false, m.get("baseEmpty"));
        assertEquals(false, m.get("builtEmpty"));
        assertEquals(true, m.get("hasB"));
        assertEquals(Map.of(), m.get("emptyMap"), "Map.empty is an empty map");
    }

    /** The Map higher-order operations ([#stdlib-map]): fold sums the values, map keeps the keys and
     *  transforms the values, update rewrites one present key through a {@code value -> value} step
     *  (an absent key is a no-op — insert / remove cover the other two cases). */
    @Test
    void foldMapUpdateOverAMap() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Map ( fold, mapValues, updateIfPresent )

                data In = { stock: Map<String, Int> }
                data Out = {
                    total: Int
                    , doubled: Map<String, Int>
                    , flagged: Map<String, Bool>
                    , afterIssue: Map<String, Int>
                    , afterAbsent: Map<String, Int>
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = {
                    Out {
                        total = fold((acc, k, v) -> acc + v, 0, i.stock),
                        doubled = mapValues((k, v) -> v * 2, i.stock),
                        flagged = mapValues((k, v) -> v > 15, i.stock),
                        afterIssue = updateIfPresent("a", (v) -> v - 1, i.stock),
                        afterAbsent = updateIfPresent("z", (v) -> v - 1, i.stock)
                    }
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("stock", Map.of("a", 10L, "b", 20L)));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(30L, m.get("total"), "fold sums every value");
        assertEquals(Map.of("a", 20L, "b", 40L), m.get("doubled"), "map keeps keys, doubles values");
        assertEquals(Map.of("a", false, "b", true), m.get("flagged"),
                "map changes the value type Int -> Bool, keeping the keys");
        assertEquals(Map.of("a", 9L, "b", 20L), m.get("afterIssue"), "update rewrites the present key");
        assertEquals(Map.of("a", 10L, "b", 20L), m.get("afterAbsent"),
                "update leaves the map unchanged when the key is absent");
    }

    /** {@code filter} and the key algebra ([#stdlib-map]). All three of union / intersect /
     *  difference answer with entries taken from the left map, so a collision keeps the left value
     *  (Elm's {@code Dict.union} is left-biased too) and nothing merges two values under one key. */
    @Test
    void filterAndTheKeyAlgebraOverMaps() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Map ( filterEntries, union, intersection, difference )

                data In = { left: Map<String, Int>, right: Map<String, Int> }
                data Out = {
                    big: Map<String, Int>
                    , joined: Map<String, Int>
                    , shared: Map<String, Int>
                    , only: Map<String, Int>
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    big = filterEntries((k, v) -> v >= 20, i.left),
                    joined = union(i.left, i.right),
                    shared = intersection(i.left, i.right),
                    only = difference(i.left, i.right)
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In",
                Map.of("left", Map.of("a", 10L, "b", 20L), "right", Map.of("b", 99L, "c", 30L)));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));

        assertEquals(Map.of("b", 20L), m.get("big"), "filter keeps the entries the predicate holds for");
        assertEquals(Map.of("a", 10L, "b", 20L, "c", 30L), m.get("joined"),
                "union adds the right map's new keys and keeps the left value for a shared key");
        assertEquals(Map.of("b", 20L), m.get("shared"), "intersect keeps the left entries whose key is shared");
        assertEquals(Map.of("a", 10L), m.get("only"), "difference keeps the left entries the right map lacks");
    }

    /** fold / map / update over a statically-typed map that is empty at runtime: fold returns the
     *  seed, map and update return an empty map — no step runs. (A bare {@code Map.empty} has no
     *  value type for a step to consume, so the meaningful empty case is a typed map, empty at run
     *  time.) */
    @Test
    void foldMapUpdateOverTheEmptyMap() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Map ( fold, mapValues, updateIfPresent )

                data In = { stock: Map<String, Int> }
                data Out = {
                    total: Int
                    , doubled: Map<String, Int>
                    , updated: Map<String, Int>
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = {
                    Out {
                        total = fold((acc, k, v) -> acc + v, 0, i.stock),
                        doubled = mapValues((k, v) -> v * 2, i.stock),
                        updated = updateIfPresent("a", (v) -> v - 1, i.stock)
                    }
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("stock", Map.of()));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(0L, m.get("total"), "fold over an empty map is the seed");
        assertEquals(Map.of(), m.get("doubled"), "map over an empty map is empty");
        assertEquals(Map.of(), m.get("updated"), "update on an absent key of an empty map is empty");
    }

    /** A {@code Map.fold} seeded with the empty list grows a list out of a map, the same shape
     *  {@code List.fold} allows. The seed carries no element type of its own, so it takes the one
     *  the result is used at — here the field the fold feeds. */
    @Test
    void foldGrowsAListFromAnEmptySeed() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Map ( fold )

                data In = { counts: Map<String, Int> }
                data Out = { lines: List<String> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    lines = fold((acc, k, v) -> acc ++ [k ++ "=" ++ String.fromInt(v)], [], i.counts)
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", Map.of("counts", Map.of("a", 2L)));
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(java.util.List.of("a=2"), m.get("lines"));
    }

    /** The same fold named on its own line: the binding's written type fixes the seed instead. */
    @Test
    void foldGrowsAListFromAnEmptySeedUnderAnAnnotatedBinding() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Map ( fold )

                data In = { counts: Map<String, Int> }
                data Out = { keys: List<String> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = {
                    let keys: List<String> = fold((acc, k, v) -> acc ++ [k], [], i.counts)
                    Out { keys = keys }
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", Map.of("counts", Map.of("a", 2L)));
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(java.util.List.of("a"), m.get("keys"));
    }

    /** upsert collapses insert-if-absent / modify-if-present: it applies the step to a present key
     *  and inserts the default for an absent one ([#stdlib-map]). */
    @Test
    void upsertInsertsWhenAbsentAndModifiesWhenPresent() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Map ( updateOrInsert )

                data In = { counts: Map<String, Int> }
                data Out = {
                    bumpedPresent: Map<String, Int>
                    , bumpedAbsent: Map<String, Int>
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = {
                    Out {
                        bumpedPresent = updateOrInsert("a", 1, (n) -> n + 1, i.counts),
                        bumpedAbsent = updateOrInsert("z", 1, (n) -> n + 1, i.counts)
                    }
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", Map.of("counts", Map.of("a", 10L, "b", 20L)));
        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(Map.of("a", 11L, "b", 20L), m.get("bumpedPresent"),
                "upsert applies the step to a present key");
        assertEquals(Map.of("a", 10L, "b", 20L, "z", 1L), m.get("bumpedAbsent"),
                "upsert inserts the default for an absent key");
    }

    /**
     * The empty map is a value: its declaration is written with no parameter list, so it takes no
     * argument list either. The spec has always said so; the implementation had it the other way,
     * and named the qualifier as a local nobody declared.
     */
    @Test
    void theEmptyMapIsWrittenWithoutAnArgumentList() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo
                data Out = { m: Map<String, Int> }
                data Req = { n: Int }
                behavior go : (r: Req) -> Out
                    constructs Out
                let go (r) = Out { m = Map.empty }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Req", Map.of("n", 1L));
        Object go = loader.loadClass("demo.Go$Impl").getConstructor().newInstance();
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(go, in));

        assertEquals(Map.of(), out.get("m"));
    }

    @Test
    void applyingTheEmptyMapIsRefusedAsApplyingAValue() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Out = { m: Map<String, Int> }
                data Req = { n: Int }
                behavior go : (r: Req) -> Out
                    constructs Out
                let go (r) = Out { m = Map.empty() }
                """));
        assertEquals("check.apply.notfunction", e.diagnostic().messageKey());
        assertTrue(e.getMessage().contains("Map.empty"), e.getMessage());
    }
}
