package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The map side of the same rewrite: a fold whose accumulator is a map it only reads and writes
 * carries a builder for the length of the walk, instead of rebuilding the trie on every element.
 * Reading is what separates this from the list case — {@code Map.updateOrInsert} looks the key up before it
 * writes — so what these tests hold is that the read answers from what the walk has written so far.
 *
 * <p>The keys are strings because that is what a map crossing the boundary may be keyed by
 * (ADR-0040), which says nothing about the rewrite: the walk is the same one whatever the key is.
 */
class CompileGrowingMapFoldTest {

    private Map<?, ?> counted(String body, List<String> xs) throws Exception {
        String src = """
                module demo
                data Bag = { xs: List<String> }
                data Out = { m: Map<String, Int> }
                behavior run : (b: Bag) -> Out constructs Out
                let run (b) = Out { m = %s }
                """.formatted(body);
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object bag = Codecs.decoded(loader, "demo.Bag", Map.of("xs", xs));
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, bag);
        return (Map<?, ?>) ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("m");
    }

    /** How many times the compiled module calls {@code method} on the runtime's map helpers. */
    private int callsTo(String src, String method) {
        int calls = 0;
        for (byte[] bytes : Compiler.compile(src).values()) {
            for (java.lang.classfile.MethodModel m : java.lang.classfile.ClassFile.of()
                    .parse(bytes).methods()) {
                if (m.code().isEmpty()) {
                    continue;
                }
                for (java.lang.classfile.CodeElement element : m.code().get()) {
                    if (element instanceof java.lang.classfile.instruction.InvokeInstruction invoke
                            && invoke.owner().asInternalName().equals("souther/runtime/Maps")
                            && invoke.name().stringValue().equals(method)) {
                        calls++;
                    }
                }
            }
        }
        return calls;
    }

    private String module(String body) {
        return """
                module demo
                behavior run : (xs: List<String>) -> Map<String, Int>
                let run (xs) = %s
                """.formatted(body);
    }

    private static Map<String, Long> expected(Object... pairs) {
        Map<String, Long> m = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            m.put((String) pairs[i], (Long) pairs[i + 1]);
        }
        return m;
    }

    private static final String TALLY =
            "List.fold((acc, x) -> Map.updateOrInsert(x, 1, c -> c + 1, acc), Map.empty, %s)";

    @Test
    void countingWithUpsertReadsWhatTheWalkHasWritten() throws Exception {
        assertEquals(expected("a", 2L, "b", 1L),
                counted(TALLY.formatted("b.xs"), List.of("a", "b", "a")));
    }

    @Test
    void anEmptyWalkGivesAnEmptyMap() throws Exception {
        assertEquals(Map.of(), counted(TALLY.formatted("b.xs"), List.of()));
    }

    @Test
    void aWalkLongerThanOneNodeWritesEveryKey() throws Exception {
        // Enough distinct keys that the trie grows past its root node, so the walk exercises the
        // builder's own nodes rather than only the first one.
        List<String> xs = new java.util.ArrayList<>();
        Map<String, Long> oracle = new LinkedHashMap<>();
        for (int i = 0; i < 200; i++) {
            xs.add("k" + i);
            oracle.put("k" + i, 1L);
        }
        assertEquals(oracle, counted(TALLY.formatted("b.xs"), xs));
    }

    @Test
    void insertingWithoutReadingWrites() throws Exception {
        assertEquals(expected("a", 1L, "b", 1L),
                counted("List.fold((acc, x) -> Map.insert(x, 1, acc), Map.empty, b.xs)",
                        List.of("a", "b")));
    }

    @Test
    void aLaterEntryWithTheSameKeyWins() throws Exception {
        assertEquals(expected("k", 3L),
                counted("List.fold((acc, x) -> Map.insert(\"k\", String.length(x), acc), "
                        + "Map.empty, b.xs)", List.of("a", "bb", "ccc")));
    }

    @Test
    void aFoldThatSkipsSomeElementsWrites() throws Exception {
        assertEquals(expected("bb", 2L),
                counted("List.fold((acc, x) -> if String.length(x) > 1 "
                        + "then Map.insert(x, String.length(x), acc) else acc, Map.empty, b.xs)",
                        List.of("a", "bb")));
    }

    @Test
    void anUpsertIsOneWalkWithABuilder() {
        String src = module(TALLY.formatted("xs"));
        assertEquals(1, callsTo(src, "builder"));
        assertEquals(0, callsTo(src, "insert"));
    }

    @Test
    void aSeedThatIsNotEmptyIsLeftAlone() throws Exception {
        String body = "List.fold((acc, x) -> Map.insert(x, 1, acc), Map.singleton(\"z\", 9), %s)";
        assertEquals(0, callsTo(module(body.formatted("xs")), "builder"));
        assertEquals(expected("z", 9L, "a", 1L), counted(body.formatted("b.xs"), List.of("a")));
    }

    @Test
    void theSizeSoFarIsRead() throws Exception {
        // Reading the accumulator's size is a read like any other: the builder answers with what the
        // walk has written so far, which is what the fold's own accumulator held there.
        String body = "List.fold((acc, x) -> Map.insert(x, Map.size(acc), acc), Map.empty, %s)";
        assertEquals(1, callsTo(module(body.formatted("xs")), "builder"));
        assertEquals(expected("a", 0L, "b", 1L), counted(body.formatted("b.xs"), List.of("a", "b")));
    }

    @Test
    void anAccumulatorGivenToSomethingThatAnswersWithAMapIsLeftAlone() throws Exception {
        // `Map.remove` answers with a map of its own, so what the insert writes into is no longer the
        // accumulator and the walk keeps the persistent insert. The answer must not change either way.
        String body = "List.fold((acc, x) -> Map.insert(x, 1, Map.remove(\"z\", acc)), "
                + "Map.empty, %s)";
        assertEquals(0, callsTo(module(body.formatted("xs")), "builder"));
        assertEquals(expected("a", 1L, "b", 1L), counted(body.formatted("b.xs"), List.of("a", "b")));
    }

    @Test
    void groupingBuildsTheBuckets() throws Exception {
        String src = """
                module demo
                data Bag = { xs: List<String> }
                data Out = { m: Map<String, List<String>> }
                behavior run : (b: Bag) -> Out constructs Out
                let run (b) = Out { m = List.groupBy(x -> x, b.xs) }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object bag = Codecs.decoded(loader, "demo.Bag", Map.of("xs", List.of("a", "b", "a")));
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, bag);
        assertEquals(Map.of("a", List.of("a", "a"), "b", List.of("b")),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("m"));
    }
}
