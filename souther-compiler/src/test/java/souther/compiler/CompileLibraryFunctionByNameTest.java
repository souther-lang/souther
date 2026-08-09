package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A named function may be handed over rather than applied, and that is one rule for every named
 * function ([#blocks]): {@code List.all(isValid, reasons)} and {@code List.all(r -> isValid(r),
 * reasons)} are the same thing. It held for a module's own {@code let} and not for the library's,
 * whose names could not be written without an argument list at all.
 *
 * <p>What a name is on the other side of — a Souther body, a shipped kernel — is not the name's
 * business, so both reach the same expansion through the declaration.
 */
class CompileLibraryFunctionByNameTest {

    private static Object run(String source, Map<String, Object> in) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source),
                CompileLibraryFunctionByNameTest.class.getClassLoader());
        Object behavior = loader.loadClass("demo.Go$Impl").getConstructor().newInstance();
        return Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", in)));
    }

    /** A library function whose implementation is a Souther body. */
    @Test
    void aLibraryHelperIsHandedOverByName() throws Exception {
        Map<?, ?> out = (Map<?, ?>) run("""
                module demo

                data In = { xs: List<String> }
                data Out = { allEmpty: Bool }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { allEmpty = List.all(String.isEmpty, i.xs) }
                """, Map.of("xs", List.of("", "")));

        assertEquals(true, out.get("allEmpty"));
    }

    /** And one whose implementation is a shipped kernel. The name does not say which. */
    @Test
    void aLibraryKernelIsHandedOverByName() throws Exception {
        Map<?, ?> out = (Map<?, ?>) run("""
                module demo

                data In = { xs: List<String> }
                data Out = { trimmed: List<String> }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { trimmed = List.map(String.trim, i.xs) }
                """, Map.of("xs", List.of("  a  ", " b")));

        assertEquals(List.of("a", "b"), out.get("trimmed"));
    }

    /**
     * The one that says a named function is really a value rather than a spelling allowed at an
     * argument: two of them chosen between at run time, then applied. Nothing about this is about
     * where the name was written.
     */
    @Test
    void twoNamedLibraryFunctionsAreChosenBetweenAtRunTime() throws Exception {
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

        assertEquals("a", ((Map<?, ?>) run(src, Map.of("s", " a ", "flag", true))).get("t"));
        assertEquals(" ab ", ((Map<?, ?>) run(src, Map.of("s", " AB ", "flag", false))).get("t"));
    }

    /** The same, mixing a library name with a block the author wrote. They are one kind of value. */
    @Test
    void aNamedFunctionAndAWrittenBlockAreOneKindOfValue() throws Exception {
        String src = """
                module demo

                data In = { s: String, flag: Bool }
                data Out = { t: String }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = {
                    let f = if i.flag then String.trim else (x) -> String.append(x, "!")
                    Out { t = f(i.s) }
                }
                """;

        assertEquals("a", ((Map<?, ?>) run(src, Map.of("s", " a ", "flag", true))).get("t"));
        assertEquals("a!", ((Map<?, ?>) run(src, Map.of("s", "a", "flag", false))).get("t"));
    }

    /**
     * An operation taking a rounding mode is an ordinary function, so handing it over expands like
     * any other name — and a two-parameter function where {@code List.map} wants one is the
     * ordinary arity mismatch, not a rule about the mode.
     */
    @Test
    void anOperationTakingARoundingModeExpandsLikeAnyOtherName() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { ds: List<Decimal> }
                data Out = { ns: List<Int> }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { ns = List.map(Decimal.toInt, i.ds) }
                """));

        assertEquals("helper.the-block-takes-another-number-of-arguments", e.diagnostic().messageKey());
    }

    /** An empty collection is a declaration with no parameter list, so it is already the value it
     * is and is not expanded into a function. */
    @Test
    void anEmptyCollectionIsNotExpandedIntoAFunction() throws Exception {
        Map<?, ?> out = (Map<?, ?>) run("""
                module demo

                data In = { n: Int }
                data Out = { m: Map<String, Int> }

                behavior go : (i: In) -> Out constructs Out

                let go (i) = Out { m = Map.empty }
                """, Map.of("n", 1L));

        assertEquals(Map.of(), out.get("m"));
    }
}
