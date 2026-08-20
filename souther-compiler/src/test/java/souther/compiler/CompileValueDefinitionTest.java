package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code let} carries its parameters on the left of {@code =}; with none written it defines a
 * value. The two shapes are what F# and Elm use to tell a value from a function, and a value is what
 * lets a name stand for a record instead of the record being written out at each use.
 *
 * <p>A value is substituted at each reference rather than held as module state, so a lambda written
 * on the right of {@code =} is the parameter-list form: the two spellings settle to one definition.
 */
class CompileValueDefinitionTest {

    private BytesClassLoader loader(String source) {
        return new BytesClassLoader(Compiler.compile(source), getClass().getClassLoader());
    }

    /** `bump` applied to `In { n }`, read back as the `n` of its `Out`. */
    private static Object bumped(BytesClassLoader loader, long n) throws Exception {
        Object behavior = Emitted.behavior(loader, "demo", "bump").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", Map.of("n", n)));
        return ((Map<?, ?>) Codecs.encode(loader, "demo.Out", out)).get("n");
    }

    @Test
    void aLetWithNoParameterListDefinesAValue() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let step = 10

                behavior bump : (i: In) -> Out constructs Out
                let bump (i) = Out { n = i.n + step }
                """);

        assertEquals(11L, bumped(loader, 1));
    }

    @Test
    void aValueMayBeARecordAndItsFieldsAreRead() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let origin = In { n = 100 }

                behavior bump : (i: In) -> Out constructs Out, In
                let bump (i) = Out { n = i.n + origin.n }
                """);

        assertEquals(101L, bumped(loader, 1));
    }

    /** A value is substituted where it is named, but what it builds is built by the definition it
     * was substituted from. The behavior that names it reads a value it did not make and answers for
     * none of it — a helper is the other case, and its body's constructions are its caller's. */
    @Test
    void whatAValueBuildsIsNotTheNamingBehaviorsToDeclare() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let origin = In { n = 100 }

                behavior bump : (i: In) -> Out constructs Out
                let bump (i) = Out { n = i.n + origin.n }
                """));
    }

    @Test
    void aLambdaOnTheRightOfEqualsIsTheParameterListForm() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let addOne = (x) -> x + 1

                behavior bump : (i: In) -> Out constructs Out
                let bump (i) = Out { n = addOne(i.n) }
                """);

        assertEquals(2L, bumped(loader, 1));
    }

    /** Only a written lambda moves its parameters to the left of {@code =}. A `.field` getter is a
     * block too, but its parameter is synthesized, so lifting it would name a definition's parameter
     * something the author never wrote; it stays a block and is refused as one. */
    @Test
    void aFieldGetterIsNotTheParameterListForm() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let read = .n

                behavior bump : (i: In) -> Out constructs Out
                let bump (i) = Out { n = read(i) }
                """));

        assertTrue(e.getMessage().contains("block is not a value"), e.getMessage());
    }

    @Test
    void anEmptyParameterListIsNotADefinitionForm() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                let step() = 10

                behavior bump : (i: In) -> Out constructs Out
                let bump (i) = Out { n = i.n + step() }
                """));

        assertTrue(e.getMessage().contains("step"), e.getMessage());
    }

    @Test
    void aValueTakesItsTypeFromItsBodyLikeAHelper() throws Exception {
        // `total` is read through the field of a value declared further down the file; the whole
        // module is read before a definition is settled, as it is for a helper's parameter.
        BytesClassLoader loader = loader("""
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                behavior bump : (i: In) -> Out constructs Out
                let bump (i) = Out { n = i.n + total }

                let total = base + 5
                let base = 20
                """);

        assertEquals(26L, bumped(loader, 1));
    }
}
