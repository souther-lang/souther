package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A helper's declared return type is a declaration into its body, and it stays one where the helper
 * is inlined: a call site whose own expected type says nothing (a generic parameter such as
 * {@code Map.toList}'s, or none at all) still fixes the accumulator of a fold over an empty seed in
 * the helper's body.
 */
class CompileHelperReturnPushdownTest {

    @Test
    void aGenericCallSiteKeepsTheHelpersDeclaredReturn() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( fold, map )

                data In = { keys: List<String> }
                data Out = { lines: List<String> }

                behavior run : (i: In) -> Out constructs Out

                let tally (keys: List<String>): Map<String, Int> =
                    fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty, keys)

                let entryKey (e: (String, Int)): String = {
                    let (k, _) = e
                    k
                }

                let run (i) = Out { lines = map(entryKey, Map.toList(tally(i.keys))) }
                """), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", Map.of("keys", List.of("a", "b", "a")));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(2, ((List<?>) out.get("lines")).size());
    }

    @Test
    void aListReturningHelperFeedsAGenericPosition() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( fold, length )

                data In = { ns: List<Int> }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out

                let doubled (ns: List<Int>): List<Int> = fold((acc, n) -> acc ++ [n * 2], [], ns)

                let run (i) = Out { n = length(List.distinct(doubled(i.ns))) }
                """), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", Map.of("ns", List.of(1L, 1L, 2L)));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(2L, out.get("n"));
    }

    /** {@code List.sortBy} takes its key as a real function value, so the backend re-types the list
     * argument to learn the element type. That argument may hold a recursive helper call (the
     * {@code foldFrom} a fold expands to), which it can only resolve with the recursive helpers'
     * signatures in scope. */
    @Test
    void sortByOverAFoldedListResolvesTheRecursiveHelper() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import List ( fold, map )

                data In = { keys: List<String> }
                data Out = { ranked: List<String> }

                behavior run : (i: In) -> Out constructs Out

                let tally (keys: List<String>): Map<String, Int> =
                    fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty, keys)

                let entryKey (e: (String, Int)): String = {
                    let (k, _) = e
                    k
                }

                let entryCount (e: (String, Int)): Int = {
                    let (_, c) = e
                    c
                }

                let run (i) = Out { ranked =
                    Map.toList(tally(i.keys))
                        |> List.sortBy(e -> entryCount(e))
                        |> List.reverse
                        |> List.take(1)
                        |> map(entryKey)
                }
                """), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", Map.of("keys", List.of("a", "b", "a")));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(List.of("a"), out.get("ranked"), "the most frequent key leads the ranking");
    }

    @Test
    void aLyingDeclaredReturnIsStillReportedAgainstTheHelper() {
        // The push-down must not turn a wrong declaration into a diagnostic about a generated binding.
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Out = { s: String }

                behavior run : (i: In) -> Out constructs Out

                let label (n: Int): String = n

                let run (i) = Out { s = label(i.n) }
                """));
        assertTrue(e.getMessage().contains("label"), e.getMessage());
        assertTrue(!e.getMessage().contains("$r"), "a generated binding name leaked: " + e.getMessage());
    }
}
