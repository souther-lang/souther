package souther.compiler;

import souther.compiler.jvm.ClassFileImage;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A fold that only grows a list builds it instead of rebuilding it: the accumulator is a builder for
 * the length of the walk and is sealed at the end. What these tests hold is that the rewrite gives
 * the same list the immutable append gave — over the combinators derived from fold ({@code map},
 * {@code filter}, {@code flatMap}, {@code filterMap}), over a fold an author wrote in that shape,
 * and over the folds that must be left alone because their accumulator is read as a list.
 */
class CompileGrowingFoldTest {

    private Object run(String body, List<?> xs, String element) throws Exception {
        String src = """
                module demo
                data Bag = { xs: List<%s> }
                data Out = { ys: List<%s> }
                behavior run : (b: Bag) -> Out constructs Out
                let run (b) = Out { ys = %s }
                """.formatted(element, element, body);
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object bag = Codecs.decoded(loader, "demo.Bag", Map.of("xs", xs));
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, bag);
        return ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("ys");
    }

    private Object ints(String body, List<Long> xs) throws Exception {
        return run(body, xs, "Int");
    }

    /** How many times the compiled module calls {@code method} on the runtime's list helpers. What
     *  this holds is that the rewrite reached the bytecode — the answers below are the same either
     *  way, so nothing else here would notice a rewrite that stopped firing. A walk is counted by the
     *  {@code builder} it starts from, the loop itself being emitted in place; two walks joined into
     *  one leave one builder behind. */
    private int callsTo(String src, String method) {
        int calls = 0;
        for (ClassFileImage emitted : Compiler.compile(src).values()) {
            for (java.lang.classfile.MethodModel m : java.lang.classfile.ClassFile.of()
                    .parse(emitted.bytes()).methods()) {
                if (m.code().isEmpty()) {
                    continue;
                }
                for (java.lang.classfile.CodeElement element : m.code().get()) {
                    if (element instanceof java.lang.classfile.instruction.InvokeInstruction invoke
                            && invoke.owner().asInternalName().equals("souther/runtime/Lists")
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
                behavior run : (xs: List<Int>) -> List<Int>
                let run (xs) = %s
                """.formatted(body);
    }

    @Test
    void aMapIsEmittedAsAWalkWithABuilder() {
        assertEquals(1, callsTo(module("List.map(x -> x * 2, xs)"), "builder"));
        assertEquals(0, callsTo(module("List.map(x -> x * 2, xs)"), "build"));
    }

    /**
     * A field of a construction an attempt is testing is body like any other, so a walk written there
     * is rewritten there. The construction is the one child of an expression that is not an
     * expression, and a pass that stopped at it would leave everything an attempt builds unrewritten
     * — silently, since the answer is the same either way.
     */
    @Test
    void aWalkInsideAnAttemptedConstructionIsRewritten() {
        assertEquals(1, callsTo("""
                module demo

                data Bag = { xs: List<Int> }
                data Doubled = { ys: List<Int> }
                    invariant List.length(ys) >= 0
                data Empty
                data Out = Doubled | Empty

                behavior run : (b: Bag) -> Out constructs Doubled
                let run (b) =
                    if Doubled { ys = List.map(x -> x * 2, b.xs) } as d then d else Empty
                """, "builder"));
    }

    @Test
    void aStepAddingAListIsEmittedAsAGrowAll() {
        assertEquals(1, callsTo(module("List.flatMap(x -> [x, x], xs)"), "growAll"));
    }

    @Test
    void aFoldReadingItsAccumulatorKeepsTheAppend() {
        String src = module("List.fold((acc, x) -> acc ++ [List.length(acc)], [], xs)");
        assertEquals(1, callsTo(src, "append"));
        assertEquals(0, callsTo(src, "builder"));
    }

    @Test
    void aMapOverAFilterIsOneWalk() {
        assertEquals(1, callsTo(module("List.map(x -> x * 2, List.filter(x -> x > 2, xs))"), "builder"));
    }

    @Test
    void threeWalksInARowAreOneWalk() {
        assertEquals(1, callsTo(
                module("List.map(x -> x + 1, List.map(x -> x * 2, List.filter(x -> x > 2, xs)))"),
                "builder"));
    }

    @Test
    void aWalkOverOneAddingAListStaysTwoWalks() {
        // The inner step adds a list where the outer step takes an element, so there is nothing to
        // put the outer step into and both walks stand.
        assertEquals(2, callsTo(module("List.map(x -> x * 2, List.flatMap(x -> [x, x], xs))"),
                "builder"));
    }

    @Test
    void mapBuildsTheMappedList() throws Exception {
        assertEquals(List.of(2L, 4L, 6L), ints("List.map(x -> x * 2, b.xs)", List.of(1L, 2L, 3L)));
    }

    @Test
    void filterBuildsTheKeptElements() throws Exception {
        assertEquals(List.of(3L, 4L),
                ints("List.filter(x -> x > 2, b.xs)", List.of(1L, 2L, 3L, 4L)));
    }

    @Test
    void aWalkLongerThanOneTailBuildsEveryElement() throws Exception {
        // The builder fills a 32-slot tail per block and spills into the trie; a walk that stays
        // inside the first tail would never exercise the spill.
        List<Long> xs = new java.util.ArrayList<>();
        List<Long> doubled = new java.util.ArrayList<>();
        for (long i = 0; i < 100; i++) {
            xs.add(i);
            doubled.add(i * 2);
        }
        assertEquals(doubled, ints("List.map(x -> x * 2, b.xs)", xs));
    }

    @Test
    void anEmptyListBuildsAnEmptyList() throws Exception {
        assertEquals(List.of(), ints("List.map(x -> x * 2, b.xs)", List.of()));
    }

    @Test
    void aFoldAnAuthorWroteInTheSameShapeBuilds() throws Exception {
        assertEquals(List.of(11L, 12L),
                ints("List.fold((acc, x) -> acc ++ [x + 10], [], b.xs)", List.of(1L, 2L)));
    }

    @Test
    void aStepThatAppendsSeveralElementsBuilds() throws Exception {
        assertEquals(List.of(1L, 1L, 2L, 2L),
                ints("List.flatMap(x -> [x, x], b.xs)", List.of(1L, 2L)));
    }

    @Test
    void aStepThatSkipsThroughAMatchBuilds() throws Exception {
        assertEquals(List.of(2L),
                ints("List.filterMap(x -> List.find(y -> y == x + 1, b.xs), b.xs)", List.of(1L, 2L)));
    }

    @Test
    void nestedFoldsBuildBoth() throws Exception {
        assertEquals(List.of(6L, 8L),
                ints("List.map(x -> x * 2, List.filter(x -> x > 2, b.xs))", List.of(1L, 2L, 3L, 4L)));
    }

    @Test
    void threeWalksJoinedGiveTheSameAnswer() throws Exception {
        assertEquals(List.of(7L, 9L),
                ints("List.map(x -> x + 1, List.map(x -> x * 2, List.filter(x -> x > 2, b.xs)))",
                        List.of(1L, 2L, 3L, 4L)));
    }

    @Test
    void aWalkJoinedOntoOneThatSkipsKeepsTheOrder() throws Exception {
        // The outer step runs where the inner one adds, so an element the inner walk drops never
        // reaches it — order and count must come out as the two separate walks gave them.
        assertEquals(List.of(20L, 40L),
                ints("List.map(x -> x * 10, List.filter(x -> x < 5, b.xs))",
                        List.of(2L, 7L, 4L, 9L)));
    }

    @Test
    void anAccumulatorReadAsAListIsLeftAlone() throws Exception {
        // The step reads the accumulator's length as well as growing it, so it is not linear and the
        // fold keeps the immutable append. What is checked is the answer, which must not change.
        assertEquals(List.of(0L, 1L, 2L),
                ints("List.fold((acc, x) -> acc ++ [List.length(acc)], [], b.xs)",
                        List.of(7L, 8L, 9L)));
    }

    @Test
    void aSeedThatIsNotEmptyIsLeftAlone() throws Exception {
        assertEquals(List.of(0L, 1L, 2L),
                ints("List.fold((acc, x) -> acc ++ [x], [0], b.xs)", List.of(1L, 2L)));
    }

    @Test
    void aFoldThatDoesNotBuildAListIsLeftAlone() throws Exception {
        String src = """
                module demo
                data Bag = { xs: List<Int> }
                data Out = Int
                behavior run : (b: Bag) -> Out constructs Out
                let run (b) = Out(List.fold((acc, x) -> acc + x, 0, b.xs))
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object bag = Codecs.decoded(loader, "demo.Bag", Map.of("xs", List.of(1L, 2L, 3L)));
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        assertEquals(6L, (long) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, bag)));
    }

    @Test
    void aBuiltListIsEqualToOneGrownByAppend() throws Exception {
        // The built list is compared against the same list reached the other way, so the two
        // representations must be equal as values — a builder that sealed its tail differently
        // (a wrong length, a shared array) would show here.
        assertEquals(ints("List.fold((acc, x) -> acc ++ [x], [0], b.xs)", List.of(1L, 2L, 3L)),
                ints("[0] ++ List.map(x -> x, b.xs)", List.of(1L, 2L, 3L)));
    }
}
