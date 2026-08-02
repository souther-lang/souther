package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A binding is what a name is, so what a program means does not depend on how its bindings are
 * spelled.
 *
 * <p>Expanding a helper splices a body written in one scope into another. Where a name meant a
 * binding, it goes on meaning it: the copy's names were settled where they were written, and moving
 * the code does not change what they say. Each of these writes one program twice — once with names
 * that collide with the ones the expansion brings in, once with names that do not — and runs both.
 */
class CompileHelperShadowingTest {

    private static Object run(String source, Map<String, Object> input) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source),
                CompileHelperShadowingTest.class.getClassLoader());
        Object go = loader.loadClass("demo.Go" + "$Impl").getDeclaredConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", input);
        return ((Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(go, in))).get("ys");
    }

    /**
     * The lambda given to {@code List.map} reads a parameter of the helper that passes it. The
     * derived combinator folds with a step written {@code (acc, x) -> ...}, and the lambda is
     * spliced inside that step — so naming the parameter {@code acc} puts a binding of that spelling
     * around a body that already reads another.
     */
    @Test
    void aLambdaReadsWhatItsOwnScopeBoundEvenWhereTheExpansionBindsThatSpelling() throws Exception {
        String source = """
                module demo
                data In = { xs: List<Int>, n: Int }
                data Out = { ys: List<Int> }

                let shifted (xs: List<Int>, %s: Int): List<Int> = List.map(e -> e + %s, xs)

                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { ys = shifted(i.xs, i.n) }
                """;
        Map<String, Object> input = Map.of("xs", List.of(1L, 2L), "n", 10L);

        assertEquals(List.of(11L, 12L), run(source.formatted("bump", "bump"), input));
        assertEquals(List.of(11L, 12L), run(source.formatted("acc", "acc"), input),
                "`acc` is the parameter, not the accumulator the fold binds around it");
        assertEquals(List.of(11L, 12L), run(source.formatted("x", "x"), input),
                "`x` is the parameter, not the element the step binds around it");
    }

    /** The same for a binding the caller writes rather than a parameter, read through two
     * expansions nested one inside the other. */
    @Test
    void aBindingReadsWhatItsOwnScopeBoundThroughTwoExpansions() throws Exception {
        String source = """
                module demo
                data In = { xs: List<Int>, n: Int }
                data Out = { ys: List<Int> }

                behavior go : (i: In) -> Out constructs Out
                let go (i) = {
                    let BOUND = i.n + 1
                    Out { ys = List.map(y -> y + BOUND, List.filter(z -> z > 0, i.xs)) }
                }
                """;
        Map<String, Object> input = Map.of("xs", List.of(1L, 2L), "n", 10L);

        assertEquals(List.of(12L, 13L), run(source.replace("BOUND", "bump"), input));
        assertEquals(List.of(12L, 13L), run(source.replace("BOUND", "acc"), input),
                "`acc` is the binding written here, through both expansions");
        assertEquals(List.of(12L, 13L), run(source.replace("BOUND", "x"), input),
                "and so is `x`, which both steps bind an element under");
    }

    /** Two expansions of one helper into one body each bring their own bindings, so the second does
     * not answer for the first. */
    @Test
    void twoExpansionsOfOneHelperKeepTheirOwnBindings() throws Exception {
        String source = """
                module demo
                data In = { xs: List<Int>, n: Int }
                data Out = { ys: List<Int> }

                let scaled (by: Int, xs: List<Int>): List<Int> = List.map(x -> x * by, xs)

                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { ys = scaled(2, i.xs) ++ scaled(3, i.xs) }
                """;
        assertEquals(List.of(2L, 4L, 3L, 6L),
                run(source, Map.of("xs", List.of(1L, 2L), "n", 0L)),
                "the second expansion's `by` is 3 and the first's is still 2");
    }
}
