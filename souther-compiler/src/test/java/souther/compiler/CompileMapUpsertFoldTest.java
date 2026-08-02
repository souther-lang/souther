package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Issue #70: a {@code fold} whose seed is an empty collection ({@code Map.empty}) must type-check
 * when the step reads and writes the accumulator's value type — the idiomatic "count occurrences into
 * a map" ({@code fold} + {@code Map.upsert}). The surrounding declared type (a record field, a helper
 * return) pins the accumulator so the empty seed no longer forces its value type to a bottom.
 */
class CompileMapUpsertFoldTest {

    // REPRO 1 (primary): fold + Map.upsert with a Map.empty seed, in a record-field context.
    @Test
    void countByLabelWithUpsertAndEmptySeed() throws Exception {
        String src = """
                module demo
                import List ( fold )
                data In = { keys: List<String> }
                data Out = { m: Map<String, Int> }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { m = fold((acc, k) -> Map.upsert(k, 1, n -> n + 1, acc), Map.empty, i.keys) }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In",
                Map.of("keys", List.of("a", "b", "a", "a", "b", "c")));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(Map.of("a", 3L, "b", 2L, "c", 1L), m.get("m"));
    }

    // The same count, keyed by Int. A Map key reaches its runtime method through an Object parameter,
    // so a key that is a primitive on the stack has to be boxed on the way in; a String key is already
    // a reference and says nothing about whether that happens. Both the write (`upsert`, inside the
    // fold's step) and the read (`get`, from a helper parameter) are keyed here, because they are
    // emitted at different places. A key left unboxed is bytecode that does not verify, so this fails
    // at class load rather than as a wrong answer.
    @Test
    void countByIntKeyWithUpsertAndEmptySeed() throws Exception {
        String src = """
                module demo
                import List ( fold )
                data In = { ns: List<Int> }
                data Out = { distinct: Int, ones: Int }
                let counted (ns: List<Int>) : Map<Int, Int> =
                    fold((acc, n) -> Map.upsert(n, 1, c -> c + 1, acc), Map.empty, ns)
                let countOf (k: Int, ns: List<Int>) : Int =
                    match Map.get(k, counted(ns)) with | Some c -> c | None -> 0
                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { distinct = Map.size(counted(i.ns)), ones = countOf(1, i.ns) }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("ns", List.of(1L, 2L, 1L, 3L, 1L)));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(3L, m.get("distinct"));
        assertEquals(3L, m.get("ones"));
    }

    // REPRO 2 (diagnostics): a helper `empty` whose declared return type is the map, used as the seed,
    // with a read-modify-write step through a helper `cur`. Previously the error was misleadingly
    // stamped inside the correct helper `cur`.
    @Test
    void countWithEmptyHelperSeedAndReadModifyWriteStep() throws Exception {
        String src = """
                module demo
                import List ( fold )
                data In = { keys: List<String> }
                data Out = { m: Map<String, Int> }
                let empty : Map<String, Int> = Map.empty
                let cur (m: Map<String, Int>, k: String): Int =
                    match Map.get(k, m) with | Some n -> n | None -> 0
                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { m = fold((acc, k) -> Map.insert(k, cur(acc, k) + 1, acc), empty(), i.keys) }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In",
                Map.of("keys", List.of("x", "y", "x")));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(Map.of("x", 2L, "y", 1L), m.get("m"));
    }

    // The expected field type reaches a fold nested under an `if`: the empty-seed fold in the
    // then-branch is pinned by the field type even though it is not the field's top expression.
    @Test
    void foldWithEmptySeedUnderAnIfBranchIsPinnedByField() throws Exception {
        String src = """
                module demo
                import List ( fold )
                data In = { keys: List<String>, on: Bool }
                data Out = { m: Map<String, Int> }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out {
                    m = if i.on
                        then fold((acc, k) -> Map.upsert(k, 1, n -> n + 1, acc), Map.empty, i.keys)
                        else Map.empty
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In",
                Map.of("keys", List.of("a", "a", "b"), "on", true));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(Map.of("a", 2L, "b", 1L), m.get("m"));
    }

    // A recursive helper returning a Map with a tail-position fold over an empty seed: the checker
    // pins the accumulator from the helper's declared return, and the backend's tail-emit path must
    // thread the same declared type so the step is materialised at that type rather than crashing on
    // a bottom accumulator (a checker-accepts / codegen-crashes gap otherwise).
    @Test
    void recursiveHelperReturningAMapFoldsOverAnEmptySeedInTailPosition() throws Exception {
        String src = """
                module demo
                import List ( fold )
                data In = { keys: List<String>, n: Int }
                data Out = { m: Map<String, Int> }
                partial let build (keys: List<String>, n: Int): Map<String, Int> =
                    if n <= 0 then fold((acc, k) -> Map.upsert(k, 1, x -> x + 1, acc), Map.empty, keys)
                    else build(keys, n - 1)
                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { m = build(i.keys, i.n) }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In",
                Map.of("keys", List.of("a", "a", "a", "b"), "n", 0L));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);
        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(Map.of("a", 3L, "b", 1L), m.get("m"));
    }
}
