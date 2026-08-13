package souther.compiler;

import souther.compiler.diag.msg.DataMessage;
import souther.compiler.diag.CompileException;
import souther.compiler.query.Compilation;


import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Type variables {@code 'a} (ADR-0028) are written only in the shipped core. A non-recursive core
 * helper that carries one is monomorphised by inline expansion — the variable resolves to the
 * concrete argument type at each call site — so no polymorphic method is emitted. A user module may
 * not write a type variable at all; that is what keeps user models bounded.
 */
class CompileTypeVariableTest {

    /** Compiles a core (reserved-namespace) module, which the user-facing guard would reject. */
    private static Map<String, byte[]> compileCore(String src) {
        Compilation compilation = Compilation.ofCoreSource(src);
        compilation.answerEverything();
        CompileException failed = compilation.failure(compilation.db().allReports());
        if (failed != null) {
            throw failed;
        }
        return compilation.classes();
    }

    @Test
    void aCoreGenericHelperMonomorphisesByInlining() throws Exception {
        // `identity` is written once with `'a`; the `Int` call site resolves it to Int on inlining.
        String core = """
                module souther.gen

                data In = { v: Int }
                data Out = { v: Int }

                behavior echo : (i: In) -> Out constructs Out

                let identity (x: 'a) = x
                let echo (i) = Out { v = identity(i.v) }
                """;
        BytesClassLoader loader = new BytesClassLoader(compileCore(core), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "souther.gen.In", Map.of("v", 7L));
        Object out = Codecs.apply(Emitted.behavior(loader, "souther.gen", "echo")
                .getConstructor().newInstance(), in);
        assertEquals(7L, ((Map<?, ?>) Codecs.encode(loader, "souther.gen.Out", out)).get("v"),
                "identity returns its argument unchanged");
    }

    @Test
    void aTypeVariableInAListPositionIsAllowedInTheCore() {
        String core = """
                module souther.gen
                let firstOr (xs: List<'a>, fallback: 'a) = fallback
                """;
        assertDoesNotThrow(() -> compileCore(core));
    }

    @Test
    void aUserModuleCannotWriteATypeVariable() {
        String user = """
                module demo
                data Out = { v: Int }
                behavior echo : (i: Out) -> Out constructs Out
                let identity (x: 'a) = x
                let echo (i) = i
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(user));
        assertEquals(true, e.getMessage().contains("type variable"), e.getMessage());
    }

    /**
     * A declared return that names a type variable reaches the body it is a declaration into.
     *
     * <p>{@code (xs: List<'a>) : List<'a>} says the result holds what the argument held, and one
     * application decides that variable once, over the parameters and the result together. So a body
     * that says nothing about what it answers — here an empty collection, which says nothing about
     * what it holds — answers what the argument decided (issue #318).
     *
     * <p>Held both ways. The empty-collection bottom fits every element type, so a call that answered
     * it would pass wherever this one does and the agreeing half alone would prove nothing: the half
     * that shows the relation is the one where the caller wants a different element and is refused.
     */
    @Test
    void aDeclaredReturnNamingAVariableReachesABodyThatSaysNothing() throws Exception {
        String core = """
                module souther.gen

                data In = { names: List<String> }
                data Out = { kept: List<String> }

                behavior run : (i: In) -> Out constructs Out

                let emptyLike (xs: List<'a>): List<'a> = []

                let run (i) = Out { kept = emptyLike(i.names) ++ i.names }
                """;
        BytesClassLoader loader = new BytesClassLoader(compileCore(core), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "souther.gen.In", Map.of("names", List.of("a", "b")));
        Object out = Codecs.apply(Emitted.behavior(loader, "souther.gen", "run")
                .getConstructor().newInstance(), in);
        assertEquals(List.of("a", "b"),
                ((Map<?, ?>) Codecs.encode(loader, "souther.gen.Out", out)).get("kept"),
                "the empty result holds Strings because the argument did");
    }

    @Test
    void andWhatItAnswersIsTheArgumentsElementAndNotWhateverThePositionWants() {
        String core = """
                module souther.gen

                data In = { names: List<String> }
                data Out = { counts: List<Int> }

                behavior run : (i: In) -> Out constructs Out

                let emptyLike (xs: List<'a>): List<'a> = []

                let run (i) = Out { counts = emptyLike(i.names) }
                """;
        CompileException e = assertThrows(CompileException.class, () -> compileCore(core));
        assertInstanceOf(DataMessage.AFieldExpectsAnotherType.class, e.diagnostic().said(),
                "the call answers a list of Strings, which the field does not take: " + e.getMessage());
    }

    /**
     * And the argument is what decides it. Two calls of one such helper at two element types are two
     * applications, and neither is held to what the other decided.
     */
    @Test
    void twoCallsOfOneVariableReturningHelperDecideSeparately() throws Exception {
        String core = """
                module souther.gen

                data In = { names: List<String>, counts: List<Int> }
                data Out = { names: List<String>, counts: List<Int> }

                behavior run : (i: In) -> Out constructs Out

                let emptyLike (xs: List<'a>): List<'a> = []

                let run (i) = Out {
                    names = emptyLike(i.names) ++ i.names,
                    counts = emptyLike(i.counts) ++ i.counts
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(compileCore(core), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "souther.gen.In",
                Map.of("names", List.of("a"), "counts", List.of(1L)));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "souther.gen.Out",
                Codecs.apply(Emitted.behavior(loader, "souther.gen", "run")
                        .getConstructor().newInstance(), in));
        assertEquals(List.of("a"), out.get("names"), "one call answers a list of Strings");
        assertEquals(List.of(1L), out.get("counts"), "the other answers a list of Ints");
    }

    /**
     * A signature relates a function parameter to a value parameter, and that reaches the caller
     * whether or not the callee applies the function.
     *
     * <p>{@code witness (f: ('a) -> Bool, x: 'a)} says {@code x} is what {@code f} takes. The lambda
     * says {@code Int}, so {@code y} is an {@code Int} — and it says so although {@code witness}
     * never applies {@code f}, which means no application inside the body reproduces the relation and
     * the lambda leaves no binding behind. Whether the callee happens to use its function parameter
     * is not something a caller's typing should turn on (issue #320).
     */
    @Test
    void aFunctionParameterTheCalleeNeverAppliesStillSaysWhatItSaid() {
        String core = """
                module souther.gen
                let witness (f: ('a) -> Bool, x: 'a) = true
                let use (y) = witness((z) -> z == 1, y)
                """;
        assertDoesNotThrow(() -> compileCore(core), "the lambda decides what `y` is");
    }

    /** And it is the lambda that decides it. One whose own body says nothing about its parameter
     * settles nothing, and the parameter is as open as it was. */
    @Test
    void aLambdaThatSaysNothingAboutItsParameterSettlesNothing() {
        String core = """
                module souther.gen
                let witness (f: ('a) -> Bool, x: 'a) = true
                let use (y) = witness((z) -> true, y)
                """;
        CompileException e = assertThrows(CompileException.class, () -> compileCore(core));
        assertEquals(true, e.getMessage().contains("`y`"),
                "`y` is still undetermined, and the report says so: " + e.getMessage());
    }
}
