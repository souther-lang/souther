package souther.compiler;

import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
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

    /** A union is one type, declared the way any other is: a call answers it, not the narrower type
     * the body happens to produce, so a {@code match} on the call opens both members. */
    @Test
    void aCallAnswersTheUnionItsHelperDeclaresOverANarrowerBody() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(UNION_HEAD + """
                behavior run : (i: In) -> Out constructs Out, A
                let j (x: A): A | B = x
                let run (i) = match j(A { a = i.n }) with
                    | A as u -> Out { n = u.a }
                    | B -> Out { n = 0 }
                """), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", Map.of("n", 7L));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(7L, out.get("n"));
    }

    /** What the body produces stands as the declared union where the helper is expanded. */
    @Test
    void aNarrowerBodyStandsAsTheDeclaredUnion() {
        Core body = checked("""
                behavior run : (i: In) -> Out constructs Out, A
                let j (x: A): A | B = x
                let run (i) = match j(A { a = i.n }) with
                    | A as u -> Out { n = u.a }
                    | B -> Out { n = 0 }
                """).behaviorBodies().get("run");
        List<Core.Widen> standing = new ArrayList<>();
        collect(body, standing);
        assertTrue(standing.stream().anyMatch(w -> w.type() instanceof Type.Union
                        && Type.show(w.value().type()).equals("A")),
                "the helper's `A` stands as `A | B` in " + standing);
    }

    /** The declared union is what the body is read against, so branches that agree only as the union
     * join there — neither a primitive and a data case, nor anything the caller expects, would
     * join them otherwise. */
    @Test
    void theBodyIsReadAgainstTheDeclaredUnion() {
        checked("""
                behavior run : (i: In) -> Out constructs Out
                let j (a: Int): Int | Missing = if a > 0 then a else Missing
                let run (i) = match j(i.n) with
                    | Int as q -> Out { n = q }
                    | Missing -> Out { n = 0 }
                """);
    }

    /** The call's own type is the union, which an arithmetic operand is not. */
    @Test
    void aCallIsNotTheNarrowerTypeItsBodyProduces() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(UNION_HEAD + """
                behavior run : (i: In) -> Out constructs Out
                let j (a: Int): Int | Missing = a
                let run (i) = Out { n = j(i.n) + 1 }
                """));
        assertTrue(e.getMessage().contains("E1324"), e.getMessage());
    }

    @Test
    void aLyingUnionDeclarationIsStillReportedAgainstTheHelper() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(UNION_HEAD + """
                behavior run : (i: In) -> Out constructs Out
                let j (n: Int): A | B = n
                let run (i) = match j(i.n) with
                    | A as u -> Out { n = u.a }
                    | B -> Out { n = 0 }
                """));
        assertTrue(e.getMessage().contains("E1812") && e.getMessage().contains("`let j`"),
                e.getMessage());
    }

    private static final String UNION_HEAD = """
            module demo

            data In = { n: Int }
            data Out = { n: Int }
            data A = { a: Int }
            data B = { b: Int }
            data Missing

            """;

    /** The module's bodies as the checker left them, asked for without generating anything. */
    private static Bodies.Elaborated checked(String behaviors) {
        Compilation compilation = Compilation.ofSource(UNION_HEAD + behaviors, "Main");
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().primary())
                        .toList(),
                "the model under test checks");
        assertNotNull(checked, "the model under test was checked");
        return checked;
    }

    private static void collect(Core e, List<Core.Widen> out) {
        if (e instanceof Core.Widen w) {
            out.add(w);
        }
        Core.forEachChild(e, child -> collect(child, out));
    }
}
