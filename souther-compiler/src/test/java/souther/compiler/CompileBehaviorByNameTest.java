package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior's name handed over is the behavior (spec {@code [#blocks]}), and that holds in every
 * position a name may be written — an argument, a binding, a branch of a choice.
 *
 * <p>The name reaches the behavior's class rather than the {@code let} behind it. A Java
 * implementation replaces the behavior, so a value that reached past it to the helper body would be
 * a second answer to the same name.
 *
 * <p>Only a behavior whose requirement set is empty is one a body may name. One that requires
 * something arrives as a {@code depends on} parameter and is a binding by the time it can be
 * written, so there is no declaration for a name to stand for.
 */
class CompileBehaviorByNameTest {

    private static Map<String, byte[]> classes(String source) {
        return Compiler.compile(source);
    }

    private static Object run(String source, Map<String, Object> in) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(classes(source),
                CompileBehaviorByNameTest.class.getClassLoader());
        Object behavior = loader.loadClass("demo.Go$Impl").getConstructor().newInstance();
        return Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", in)));
    }

    private static final String TWICE = """
            module demo

            data In = { xs: List<Int> }
            data Out = { ys: List<Int> }

            behavior twice : (n: Int) -> Int
            let twice (n) = n * 2

            behavior go : (i: In) -> Out constructs Out
            """;

    /** The position that already worked: the name written where the combinator takes a function. */
    @Test
    void aBehaviorIsHandedToACombinatorByName() throws Exception {
        Map<?, ?> out = (Map<?, ?>) run(TWICE + """

                let go (i) = Out { ys = List.map(twice, i.xs) }
                """, Map.of("xs", List.of(1L, 2L, 3L)));

        assertEquals(List.of(2L, 4L, 6L), out.get("ys"));
    }

    /** The position that did not: the same name, bound to a {@code let} first. */
    @Test
    void aBehaviorIsBoundToALetAndHandedOver() throws Exception {
        Map<?, ?> out = (Map<?, ?>) run(TWICE + """

                let go (i) = {
                    let f = twice
                    Out { ys = List.map(f, i.xs) }
                }
                """, Map.of("xs", List.of(1L, 2L, 3L)));

        assertEquals(List.of(2L, 4L, 6L), out.get("ys"));
    }

    /** Bound and then applied, which is the other thing a binding holding a function is for. */
    @Test
    void aBehaviorBoundToALetIsApplied() throws Exception {
        Map<?, ?> out = (Map<?, ?>) run(TWICE + """

                let go (i) = {
                    let f = twice
                    Out { ys = [f(21)] }
                }
                """, Map.of("xs", List.of()));

        assertEquals(List.of(42L), out.get("ys"));
    }

    /**
     * A behavior and a block the author wrote are one kind of value: chosen between at run time and
     * then handed over. Nothing downstream tells which branch the value came from.
     */
    @Test
    void aBehaviorAndAWrittenBlockAreOneKindOfValue() throws Exception {
        String src = """
                module demo

                data In = { n: Int, flag: Bool }
                data Out = { ys: List<Int> }

                behavior twice : (n: Int) -> Int
                let twice (n) = n * 2

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let f = if i.flag then twice else (n) -> n + 1
                    Out { ys = [f(i.n)] }
                }
                """;

        assertEquals(List.of(42L),
                ((Map<?, ?>) run(src, Map.of("n", 21L, "flag", true))).get("ys"));
        assertEquals(List.of(22L),
                ((Map<?, ?>) run(src, Map.of("n", 21L, "flag", false))).get("ys"));
    }

    /** A behavior another module declares, bound to a {@code let} in the module that imports it. */
    @Test
    void anImportedBehaviorIsBoundToALetAndHandedOver() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module up exposing ( twice )

                behavior twice : (n: Int) -> Int
                let twice (n) = n * 2
                """, """
                module demo

                import up ( twice )

                data In = { xs: List<Int> }
                data Out = { ys: List<Int> }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let f = twice
                    Out { ys = List.map(f, i.xs) }
                }
                """));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Object behavior = loader.loadClass("demo.Go$Impl").getConstructor().newInstance();
        assertEquals(List.of(2L, 4L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Out",
                        Codecs.apply(behavior, Codecs.decoded(loader, "demo.In",
                                Map.of("xs", List.of(1L, 2L)))))).get("ys"));
    }

    /**
     * The value goes through the behavior's class. A behavior is what a Java implementation
     * replaces, so a value that reached the {@code let} instead would keep running the Souther body
     * after the behavior had been replaced.
     */
    @Test
    void theBoundNameReachesTheBehaviorAndNotTheLetBehindIt() {
        String bound = new String(classes(TWICE + """

                let go (i) = {
                    let f = twice
                    Out { ys = List.map(f, i.xs) }
                }
                """).get("demo.Go$Impl"), java.nio.charset.StandardCharsets.ISO_8859_1);

        assertTrue(bound.contains("demo/Twice"), "the expansion does not reach `demo.Twice`");
    }

    /** A binding in force wins over the declaration it shadows, here as anywhere else. */
    @Test
    void aBindingSpelledLikeABehaviorIsTheBinding() throws Exception {
        Map<?, ?> out = (Map<?, ?>) run(TWICE + """

                let go (i) = {
                    let twice = (n) -> n + 1
                    let f = twice
                    Out { ys = List.map(f, i.xs) }
                }
                """, Map.of("xs", List.of(1L, 2L)));

        assertEquals(List.of(2L, 3L), out.get("ys"));
    }

    /**
     * A behavior that requires something is not a name a body may stand for. It is reached through
     * the {@code depends on} clause that names it, which makes it a binding rather than a
     * declaration — so there is nothing here for a value to be.
     */
    @Test
    void aBehaviorThatRequiresSomethingIsNotBoundByName() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { xs: List<Int> }
                data Out = { ys: List<Int> }

                behavior scale : (n: Int) -> Int

                behavior go : (i: In) -> Out
                    constructs Out
                    depends on scale

                let go (i, scaled) = {
                    let f = scale
                    Out { ys = List.map(f, i.xs) }
                }
                """));
        assertTrue(e.getMessage().contains("`scale`"), e.getMessage());
    }

    /** A composition is composed with, not handed over: its requirements are inferred rather than
     * written, so a body resting on one would take on a set that changes with an upstream stage. */
    @Test
    void aCompositionIsNotBoundByName() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo exposing ( In, Mid, Out, one, two, chain : Out, go )

                data In = { n: Int }
                data Mid = { n: Int }
                data Out = { n: Int }

                behavior one : (i: In) -> Mid constructs Mid
                let one (i) = Mid { n = i.n }

                behavior two : (m: Mid) -> Out constructs Out
                let two (m) = Out { n = m.n }

                behavior chain = one >-> two

                behavior go : (i: In) -> Out
                let go (i) = {
                    let f = chain
                    f(i)
                }
                """));
        assertTrue(e.getMessage().contains("`chain` is a behavior"), e.getMessage());
    }
}
