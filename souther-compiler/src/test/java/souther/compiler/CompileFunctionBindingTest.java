package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A function value is bound by a {@code let} like any other value, and what it was written as does
 * not decide that: a lambda the author spelled, a library name, a module's own {@code let}, a
 * choice an {@code if} makes between them, and a binding that already holds one all reach the same
 * binding.
 *
 * <p>What is still refused is escape. A function bound and applied never becomes a runtime value —
 * it expands at the application — so the binding costs nothing; one that is carried off does, and
 * that is a separate question ([#blocks]).
 */
class CompileFunctionBindingTest {

    private static Map<?, ?> run(String source, Map<String, Object> in) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source),
                CompileFunctionBindingTest.class.getClassLoader());
        Object behavior = loader.loadClass("demo.Go$Impl").getConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", in)));
    }

    @Test
    void aLibraryFunctionIsBoundAndApplied() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { a: String, b: String }
                data Out = { x: String, y: String }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let f = String.trim
                    Out { x = f(i.a), y = f(i.b) }
                }
                """, Map.of("a", " p ", "b", " q "));

        assertEquals("p", out.get("x"));
        assertEquals("q", out.get("y"));
    }

    @Test
    void aModulesOwnHelperIsBoundAndApplied() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                let bump (x: Int) = x + 1

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let f = bump
                    Out { m = f(i.n) }
                }
                """, Map.of("n", 4L));

        assertEquals(5L, out.get("m"));
    }

    /** A binding that holds a function, read into another binding: the second names the same one. */
    @Test
    void aBindingHoldingAFunctionIsReadIntoAnother() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let f = (x) -> x + 1
                    let g = f
                    Out { m = g(i.n) }
                }
                """, Map.of("n", 10L));

        assertEquals(11L, out.get("m"));
    }

    @Test
    void aChoiceBetweenTwoLibraryFunctionsIsBoundAndApplied() throws Exception {
        String src = """
                module demo

                data In = { s: String, flag: Bool }
                data Out = { t: String }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let f = if i.flag then String.trim else String.lowercase
                    Out { t = f(i.s) }
                }
                """;

        assertEquals("a", run(src, Map.of("s", " a ", "flag", true)).get("t"));
        assertEquals(" ab ", run(src, Map.of("s", " AB ", "flag", false)).get("t"));
    }

    /** A helper answering a function, applied where it stands. */
    @Test
    void aHelperAnswersAFunction() throws Exception {
        String src = """
                module demo

                data In = { s: String, flag: Bool }
                data Out = { t: String }

                let choose (flag: Bool) : (String) -> String =
                    if flag then String.trim else String.lowercase

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { t = choose(i.flag)(i.s) }
                """;

        assertEquals("a", run(src, Map.of("s", " a ", "flag", true)).get("t"));
    }

    /** And one answering a function that captures what it was given. */
    @Test
    void aHelperAnswersAFunctionThatCapturesItsArgument() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { s: String }
                data Out = { t: String }

                let prefix (p: String) : (String) -> String = (s) -> String.append(p, s)

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { t = prefix(">")(i.s) }
                """, Map.of("s", "here"));

        assertEquals(">here", out.get("t"));
    }

    /**
     * A recursive helper is a static method, reached by the name it is declared under. Bound and
     * applied that is still what happens.
     *
     * <p>Storing one is refused, but not for being recursive: a lambda the author wrote is refused
     * there too, and for the same reason ([#blocks]). The pair below says which of the two rules is
     * doing the refusing.
     */
    @Test
    void aRecursiveHelperIsBoundAndAppliedButIsNotStored() throws Exception {
        String bound = """
                module demo

                data Tree = { child: Option<Tree> }
                data In = { root: Tree }
                data Out = { depth: Int }

                let depthOf (t: Tree): Int = match t.child with
                    | Some c -> depthOf(c) + 1
                    | None -> 0

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let d = depthOf
                    Out { depth = d(i.root) }
                }
                """;
        assertEquals(2L, run(bound, Map.of("root",
                Map.of("child", Map.of("child", Map.of())))).get("depth"));

        assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Tree = { child: Option<Tree> }
                data In = { root: Tree }
                data Out = { n: Int }

                let depthOf (t: Tree): Int = match t.child with
                    | Some c -> depthOf(c) + 1
                    | None -> 0

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let d = depthOf
                    Out { n = List.length([d]) }
                }
                """));
    }

    /**
     * A bound function that itself takes a function is not yet reached: the binding holds the block
     * the name expanded to, and a block written at one of its parameters has nothing to be checked
     * against there. Bound where it is refused so the day it is allowed is a deliberate one.
     */
    @Test
    void aBoundFunctionThatTakesAFunctionIsNotYetReached() {
        assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { ns: List<Int> }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let m = List.map
                    Out { m = List.length(m((n) -> n + 1, i.ns)) }
                }
                """));
    }

    /** A bound function taking no function is reached, whatever its declaration's type variables. */
    @Test
    void aBoundGenericFunctionTakingNoFunctionIsApplied() throws Exception {
        Map<?, ?> out = run("""
                module demo

                data In = { ns: List<Int> }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let r = List.reverse
                    Out { m = List.length(r(i.ns)) }
                }
                """, Map.of("ns", List.of(1L, 2L, 3L)));

        assertEquals(3L, out.get("m"));
    }

    /**
     * Storing a function is refused by one rule, whatever the function was written as. A recursive
     * helper is not a special case of it: the lambda beside it is refused identically, so nothing
     * about recursion is what decides this.
     */
    @Test
    void storingAFunctionIsRefusedWhateverItWasWrittenAs() {
        String lambda = """
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let w = (n) -> n + 1
                    Out { m = List.length([w]) }
                }
                """;
        String libraryName = """
                module demo

                data In = { n: Int }
                data Out = { m: Int }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let w = String.trim
                    Out { m = List.length([w]) }
                }
                """;

        for (String src : List.of(lambda, libraryName)) {
            CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
            assertEquals("check.block.notvalue", e.diagnostic().messageKey(), e.getMessage());
        }
    }
}
