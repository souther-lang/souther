package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

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

    @Test
    void aBehaviorsNameIsAnElementOfAList() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { n: Int }
                data Out = { ms: List<Int> }

                behavior twice : (n: Int) -> Int
                let twice (n) = n * 2

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { ms = List.map((f) -> f(i.n), [twice]) }
                """, Map.of("n", 4L));

        assertEquals(List.of(8L), out.get("ms"));
    }

    @Test
    void aRecursiveHelpersNameIsAnElementOfAList() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data Tree = { child: Option<Tree> }
                data In = { root: Tree }
                data Out = { ds: List<Int> }

                let depthOf (t: Tree): Int = match t.child with
                    | Some c -> depthOf(c) + 1
                    | None -> 0

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { ds = List.map((f) -> f(i.root), [depthOf]) }
                """, Map.of("root", Map.of("child", Map.of("child", Map.of()))));

        assertEquals(List.of(2L), out.get("ds"));
    }

    /** What a name is does not change with whether it was given a second name first. */
    @Test
    void aNameBoundBeforeItIsStoredIsTheSameFunction() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { xs: List<String> }
                data Out = { ts: List<String> }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let f = String.trim
                    let fs = [f]
                    Out { ts = List.map((g) -> g(" a "), fs) }
                }
                """, Map.of("xs", List.of()));

        assertEquals(List.of("a"), out.get("ts"));
    }

    /** A choice between names that declare one type is a function of that type. */
    @Test
    void aChoiceBetweenNamesTakesTheirDeclaredType() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { flag: Bool }
                data Out = { ts: List<String> }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let f = if i.flag then String.trim else String.lowercase
                    Out { ts = List.map((g) -> g(" A "), [f]) }
                }
                """, Map.of("flag", false));

        assertEquals(List.of(" a "), out.get("ts"));
    }

    /** A function handed to a helper's parameter is read against the whole function type declared. */
    @Test
    void aLambdaAnsweringAFunctionIsHandedToAFunctionParameter() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { a: Int, b: Int }
                data Out = { m: Int, t: String }

                let use (f: (Int) -> (Int) -> Int): Int = f(1)(2)
                let trimmedBy (f: (Int) -> (String) -> String): String = f(1)(" a ")

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { m = use((x) -> (y) -> x + y + i.a),
                                   t = trimmedBy((x) -> String.trim) }
                """, Map.of("a", 10L, "b", 0L));

        assertEquals(13L, out.get("m"));
        assertEquals("a", out.get("t"));
    }

    /** The name of a helper another module declares is the function that module declared. */
    @Test
    void aHelperAnotherModuleDeclaresIsAnElementOfAList() {
        Compiler.compileModules(List.of("""
                module lib

                data Box = { n: Int }

                let unbox (b: Box): Int = b.n
                """, """
                module app

                import lib ( Box, unbox )

                data In = { n: Int }
                data Out = { ms: List<Int> }

                behavior go : (i: In) -> Out constructs Out, Box

                let go (i) = Out { ms = List.map((f) -> f(Box { n = i.n }), [unbox]) }
                """));
    }

    /** A declaration with a type variable says nothing until something instantiates it. */
    @Test
    void aGenericNameNothingInstantiatesIsRefused() {
        assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { m = List.length([List.map]) }
                """));
    }

    /** A lambda no position types and nothing applies has no function type to stand at. */
    @Test
    void anUntypedLambdaNothingAppliesIsRefused() {
        assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { m = List.length([(x) -> x]) }
                """));
    }
}
