package souther.compiler;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;
import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.params.provider.Arguments.arguments;

import java.util.stream.Stream;

/**
 * The pattern of {@code String.matches} may be written as a composition (issue #208): several types
 * whose formats share a part hold that part once and vary the rest, instead of spelling the shared
 * tail out in each of them.
 *
 * <p>What the pattern must be is that it evaluates to a string at compile time, which a literal does
 * and so does a {@code ++} of literals and of named string values. Two readers ask for that string —
 * the check, which compiles the regex to prove it well-formed, and the codec derivation, which
 * carries it to the boundary as Raoh's {@code pattern} constraint — and they must not disagree about
 * which patterns are compile-time strings or about what string one composes to. So each expression
 * here is run through both.
 */
class CompileComposedPatternTest {

    /** Declarations the pattern expression may name, the expression itself, and the string it
     *  composes to. The format is NNN-NNNN throughout, so one pair of values exercises them all. */
    static Stream<Arguments> patterns() {
        return Stream.of(
                arguments("two literals", "", "\"[0-9]{3}\" ++ \"-[0-9]{4}\""),
                arguments("a named value and a literal", "let prefix = \"[0-9]{3}\"",
                        "prefix ++ \"-[0-9]{4}\""),
                arguments("two named values",
                        "let prefix = \"[0-9]{3}\"\nlet tail = \"-[0-9]{4}\"", "prefix ++ tail"),
                arguments("a value that is itself a composition",
                        "let prefix = \"[0-9]{3}\"\nlet tail = \"-[0-9]{4}\"\nlet postal = prefix ++ tail",
                        "postal"),
                arguments("three parts", "", "\"[0-9]{3}\" ++ \"-\" ++ \"[0-9]{4}\""),
                arguments("a parenthesised composition", "",
                        "(\"[0-9]{3}\" ++ \"-\") ++ \"[0-9]{4}\""),
                // Neither part is a well-formed regex alone; the composition is. What is validated is
                // therefore the composed string, not the pieces it was written in.
                arguments("parts that are regexes only once composed", "let head = \"[0-9\"",
                        "head ++ \"]{3}-[0-9]{4}\""));
    }

    private static final String MATCHING = "123-4567";
    private static final String NOT_MATCHING = "12-345";
    private static final String COMPOSED = "[0-9]{3}-[0-9]{4}";

    /** The check's reading: the composed pattern is a compile-time string, so the module compiles and
     *  the regex that runs is the composed one. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("patterns")
    void aComposedPatternIsTheRegexABehaviorRuns(String name, String decls, String pattern)
            throws Exception {
        String src = """
                module demo
                %s
                data In = { s: String }
                data Out = Bool
                behavior check : (i: In) -> Out constructs Out
                let check (i) = Out(String.matches(%s, i.s))
                """.formatted(decls, pattern);
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object behavior = loader.loadClass("demo.Check$Impl").getDeclaredConstructor().newInstance();
        assertEquals(true, runs(loader, behavior, MATCHING), "the composed pattern matches NNN-NNNN");
        assertEquals(false, runs(loader, behavior, NOT_MATCHING), "and rejects what it does not");
    }

    /** The codec derivation's reading of the same expression: the invariant reaches the boundary as
     *  Raoh's format constraint, carrying the fully composed pattern. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("patterns")
    void aComposedPatternReachesTheBoundaryAsTheFormat(String name, String decls, String pattern)
            throws Exception {
        String src = """
                module demo
                %s
                data V = String
                    invariant String.matches(%s, value)
                """.formatted(decls, pattern);
        ClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Decoder<Object, ?> dec = Codecs.decoder(loader, "demo.V");
        assertTrue(dec.decode(MATCHING, Path.ROOT) instanceof Ok, "the value has the composed format");
        Result<?> r = dec.decode(NOT_MATCHING, Path.ROOT);
        assertTrue(r instanceof Err, "this one does not, so decoding fails");
        List<Issue> issues = ((Err<?>) r).issues().asList();
        assertEquals(1, issues.size(), "one broken rule, one issue");
        assertEquals("invalid_format", issues.get(0).code(), "the format constraint, not a fallback");
        assertEquals(COMPOSED, issues.get(0).meta().get("pattern"), "composed, not left as written");
    }

    /** A composition that is malformed as a whole is a compile error, reported as the regex it
     *  composes to — the same reading the check would give a literal spelt out that way. */
    @Test
    void aCompositionThatIsNotAValidRegexIsACompileError() {
        String src = """
                module demo
                data V = String
                    invariant String.matches("[0-9]{3}" ++ "[", value)
                """;
        CompileException ex = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertTrue(ex.getMessage().contains("not a valid regular expression"),
                "the composed regex is what is compiled: " + ex.getMessage());
    }

    /** The part held once may be held by another module: what a value denotes is settled where it is
     *  written, so a published one composes here like one of this module's own. */
    @Test
    void aPublishedValueComposesInTheReadersPattern() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module formats exposing ( prefix )
                let prefix = "[0-9]{3}"
                """, """
                module ids exposing ( In, Out, check )
                import formats ( prefix )
                data In = { s: String }
                data Out = Bool
                behavior check : (i: In) -> Out constructs Out
                let check (i) = Out(String.matches(prefix ++ "-[0-9]{4}", i.s))
                """)));
    }

    /** A helper's body is read where it is written, before it lands in the body that calls it, so a
     *  malformed composition is reported there — whether or not anything calls the helper. */
    @Test
    void aMalformedCompositionInsideAnUncalledHelperIsStillReported() {
        CompileException ex = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                let prefix = "[0-9]{3}"
                let unused (s: String) = String.matches(prefix ++ "[", s)
                data In = { s: String }
                data Out = Bool
                behavior check : (i: In) -> Out constructs Out
                let check (i) = Out(true)
                """));
        assertTrue(ex.getMessage().contains("not a valid regular expression"), ex.getMessage());
    }

    /** A pattern only run time can produce is still refused: the composition rule extends what counts
     *  as a compile-time string, it does not admit a computed one. */
    @Test
    void aPatternPartlyComputedAtRunTimeIsStillRefused() {
        String src = """
                module demo
                data In = { s: String }
                data Out = Bool
                behavior check : (i: In) -> Out constructs Out
                let check (i) = Out(String.matches(i.s ++ "[0-9]{3}", i.s))
                """;
        CompileException ex = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertTrue(ex.getMessage().contains("at compile time"),
                "the pattern must evaluate at compile time: " + ex.getMessage());
    }

    private boolean runs(BytesClassLoader loader, Object behavior, String s) throws Exception {
        Object in = Codecs.decoded(loader, "demo.In", java.util.Map.of("s", s));
        return (boolean) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
    }
}
