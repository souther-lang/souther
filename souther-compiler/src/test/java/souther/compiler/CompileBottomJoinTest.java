package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Issue #74: where two branches of an {@code if} or {@code match} join, an empty-collection bottom
 * takes on the other branch's type. This held for {@code []} but not for {@code Set.empty()} or
 * {@code Map.empty()}, so a branchy fold step that returns the bare accumulator on one side was
 * rejected as soon as the accumulator was a set or a map. The same join now recurses through every
 * container — sets, maps, options, and tuples of them — in both {@code if} and {@code match}.
 */
class CompileBottomJoinTest {

    private BytesClassLoader loader(String module) {
        return new BytesClassLoader(Compiler.compile(module), getClass().getClassLoader());
    }

    private Map<?, ?> run(BytesClassLoader loader, Map<String, Object> fields) throws Exception {
        Object in = Codecs.decoded(loader, "demo.In", fields);
        Object behavior = loader.loadClass("demo.Work" + "$Impl").getDeclaredConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
    }

    /** A {@code Set.empty()}-seeded fold whose step returns the bare accumulator on one branch. */
    @Test
    void setSeedWithBranchReturningTheAccumulator() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                import List ( fold )

                data In = { xs: List<Int> }
                data Out = { n: Int }

                behavior work : (i: In) -> Out constructs Out
                let work (i) = {
                    let seen = fold((acc, x) -> if x > 0 then Set.insert(x, acc) else acc,
                        Set.empty(), i.xs)
                    Out { n = Set.size(seen) }
                }
                """);
        assertEquals(2L, run(loader, Map.of("xs", List.of(1, -1, 2, -2, 1))).get("n"));
    }

    /** The same shape with a {@code Map.empty()} seed. */
    @Test
    void mapSeedWithBranchReturningTheAccumulator() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                import List ( fold )

                data In = { xs: List<Int> }
                data Out = { n: Int }

                behavior work : (i: In) -> Out constructs Out
                let work (i) = {
                    let m = fold((acc, x) -> if x > 0 then Map.insert(x, x, acc) else acc,
                        Map.empty(), i.xs)
                    Out { n = Map.size(m) }
                }
                """);
        assertEquals(2L, run(loader, Map.of("xs", List.of(1, -1, 2, -2, 1))).get("n"));
    }

    /** The issue's own repro: a {@code (Set, List)} accumulator whose step returns a different tuple
     * expression per branch — {@code distinct} written the natural way. */
    @Test
    void tupleOfSetAndListWithBranchyStep() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                import List ( fold )

                data In = { xs: List<Int> }
                data Out = { ys: List<Int> }

                behavior work : (i: In) -> Out constructs Out
                let work (i) = {
                    let (_, out) = fold((acc, x) -> {
                        let (seen, ys) = acc
                        if Set.contains(x, seen) then (seen, ys) else (Set.insert(x, seen), ys ++ [x])
                    }, (Set.empty(), []), i.xs)
                    Out { ys = out }
                }
                """);
        assertEquals(List.of(3L, 1L, 2L), run(loader, Map.of("xs", List.of(3, 1, 3, 2, 1))).get("ys"));
    }

    /** {@code match} arms join the same way {@code if} branches do: a tuple accumulator seeded with
     * two empty lists, grown on a different side per arm. */
    @Test
    void tupleAccumulatorAcrossMatchArms() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                import List ( fold )

                data In = { xs: List<Int> }
                data Out = { ys: List<Int> }

                behavior work : (i: In) -> Out constructs Out
                let work (i) = {
                    let (positives, _) = fold((acc, x) -> {
                        let (ps, ns) = acc
                        match Int.remainder(x, 2) with
                            | Int r -> (ps ++ [r], ns)
                            | DivisionByZero -> (ps, ns ++ [x])
                    }, ([], []), i.xs)
                    Out { ys = positives }
                }
                """);
        assertEquals(List.of(1L, 0L, 1L), run(loader, Map.of("xs", List.of(1, 2, 3))).get("ys"));
    }

    /** A written type on the seed reaches the backend too: the closure is materialised at the
     * annotated element type rather than at the bottom {@code Set.empty()} carries on its own. */
    @Test
    void annotatedSetSeedReachesTheBackend() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                import List ( fold )

                data In = { xs: List<Int> }
                data Out = { n: Int }

                behavior work : (i: In) -> Out constructs Out
                let work (i) = {
                    let seed: Set<Int> = Set.empty()
                    let seen = fold((acc, x) -> if x > 0 then Set.insert(x, acc) else acc, seed, i.xs)
                    Out { n = Set.size(seen) }
                }
                """);
        assertEquals(2L, run(loader, Map.of("xs", List.of(1, -1, 2, 1))).get("n"));
    }

    /** A written type on the seed reaches the step's closure, not just the step's own result: the
     * updater of {@code Map.upsert} reads the map's value type, which only the annotation supplies
     * when the surrounding context expects something else (here an {@code Int} field). */
    @Test
    void annotatedMapSeedReachesTheStepClosure() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                import List ( fold )

                data In = { ks: List<String> }
                data Out = { n: Int }

                behavior work : (i: In) -> Out constructs Out
                let work (i) = {
                    let seed: Map<String, Int> = Map.empty()
                    let counts = fold((acc, k) -> Map.upsert(k, 1, n -> n + 1, acc), seed, i.ks)
                    Out { n = Map.size(counts) }
                }
                """);
        assertEquals(3L, run(loader, Map.of("ks", List.of("a", "b", "a", "c"))).get("n"));
    }

    /** The same through a tuple: the written component types reach the empty collections the tuple
     * seeds, so the {@code Map.upsert} updater inside the step reads a concrete value type. */
    @Test
    void annotatedTupleSeedReachesTheStepClosure() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                import List ( fold )

                data In = { ks: List<String> }
                data Out = { n: Int }

                behavior work : (i: In) -> Out constructs Out
                let work (i) = {
                    let seed: (Map<String, Int>, List<String>) = (Map.empty(), [])
                    let (counts, _) = fold((acc, k) -> {
                        let (m, order) = acc
                        let grown = Map.upsert(k, 1, n -> n + 1, m)
                        (grown, order ++ [k])
                    }, seed, i.ks)
                    Out { n = Map.size(counts) }
                }
                """);
        assertEquals(3L, run(loader, Map.of("ks", List.of("a", "b", "a", "c"))).get("n"));
    }

    /** {@code []} adopts a pushed-down type in the backend as {@code Map.empty}/{@code Set.empty} do.
     * Without it an annotated empty list binds at {@code List<_>} during emission, so reading an
     * element back yields an {@code Option<_>} and the arm unboxes a bottom — invalid bytecode. */
    @Test
    void annotatedEmptyListReachesTheBackend() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { k: Int }
                data Out = { n: Int }

                behavior work : (i: In) -> Out constructs Out
                let work (i) = {
                    let xs: List<Int> = []
                    let v = match List.get(0, xs) with | Some n -> n + 1 | None -> 0
                    Out { n = v }
                }
                """);
        assertEquals(0L, run(loader, Map.of("k", 1)).get("n"));
    }

    /** The same through a written tuple type: the component {@code List<Int>} reaches the {@code []}
     * the tuple holds. */
    @Test
    void annotatedEmptyListInsideATupleReachesTheBackend() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { k: Int }
                data Out = { n: Int }

                behavior work : (i: In) -> Out constructs Out
                let work (i) = {
                    let seed: (List<Int>, Int) = ([], 0)
                    let (xs, _) = seed
                    let v = match List.get(0, xs) with | Some n -> n + 1 | None -> 0
                    Out { n = v }
                }
                """);
        assertEquals(0L, run(loader, Map.of("k", 1)).get("n"));
    }

    /** {@code List.distinct} is written in the branchy form this join permits: the skip branch
     * returns the accumulator untouched. First occurrences are kept, in order. */
    @Test
    void distinctKeepsFirstOccurrencesInOrder() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { xs: List<Int> }
                data Out = { ys: List<Int> }

                behavior work : (i: In) -> Out constructs Out
                let work (i) = Out { ys = List.distinct(i.xs) }
                """);
        assertEquals(List.of(3L, 1L, 2L),
                run(loader, Map.of("xs", List.of(3, 1, 3, 2, 1, 3))).get("ys"));
        assertEquals(List.of(), run(loader, Map.of("xs", List.of())).get("ys"));
    }

    /** A written tuple type reaches each element, so the empty collections it seeds are concrete
     * before the step is checked. */
    @Test
    void annotatedTupleSeedPinsEachElement() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                import List ( fold )

                data In = { xs: List<Int> }
                data Out = { ys: List<Int> }

                behavior work : (i: In) -> Out constructs Out
                let work (i) = {
                    let seed: (Set<Int>, List<Int>) = (Set.empty(), [])
                    let (_, out) = fold((acc, x) -> {
                        let (seen, ys) = acc
                        if Set.contains(x, seen) then (seen, ys) else (Set.insert(x, seen), ys ++ [x])
                    }, seed, i.xs)
                    Out { ys = out }
                }
                """);
        assertEquals(List.of(3L, 1L, 2L), run(loader, Map.of("xs", List.of(3, 1, 3, 2, 1))).get("ys"));
    }
}
