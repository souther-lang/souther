package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A function is a value wherever a value goes: a lambda answering one, a library name held in a
 * collection, and a fold step answering one are typed at the function type their position gives
 * them, or the type the name's declaration gives it.
 */
class AFunctionReturnedOrNamedWhereAValueGoesIsTypedTest {

    private static Map<?, ?> run(String source, Map<String, Object> in) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source),
                AFunctionReturnedOrNamedWhereAValueGoesIsTypedTest.class.getClassLoader());
        Object behavior = Emitted.behavior(loader, "demo", "go").getConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", in)));
    }

    @Test
    void aLambdaAnswersALibraryFunction() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { n: Int, s: String }
                data Out = { t: String }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let outer: (Int) -> (String) -> String = (x) -> String.trim
                    Out { t = outer(i.n)(i.s) }
                }
                """, Map.of("n", 1L, "s", " a "));

        assertEquals("a", out.get("t"));
    }

    @Test
    void aLambdaAnswersALambda() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { a: Int, b: Int }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let outer: (Int) -> (Int) -> Int = (x) -> (y) -> x + y
                    Out { m = outer(i.a)(i.b) }
                }
                """, Map.of("a", 3L, "b", 4L));

        assertEquals(7L, out.get("m"));
    }

    @Test
    void aLibraryFunctionIsAnElementOfAListAGrowingFoldBuilds() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { xs: List<String>, s: String }
                data Out = { ts: List<String> }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let fs = List.fold((acc, x) -> acc ++ [String.trim], [], i.xs)
                    Out { ts = List.map((f) -> f(i.s), fs) }
                }
                """, Map.of("xs", List.of("p", "q"), "s", " a "));

        assertEquals(List.of("a", "a"), out.get("ts"));
    }

    @Test
    void aFoldStepAnswersAFunction() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { xs: List<Int>, n: Int }
                data Out = { m: Int }

                let id (n: Int) = n

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let f = List.fold((acc, x) -> (m) -> acc(m) + x, id, i.xs)
                    Out { m = f(i.n) }
                }
                """, Map.of("xs", List.of(1L, 2L, 3L), "n", 10L));

        assertEquals(16L, out.get("m"));
    }
}
