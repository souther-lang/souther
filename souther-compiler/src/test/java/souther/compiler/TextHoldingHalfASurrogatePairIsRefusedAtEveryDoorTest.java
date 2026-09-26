package souther.compiler;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.msg.ParseMessage;
import souther.compiler.diag.msg.TypeMessage;
import souther.compiler.generated.JsonBoundary;
import souther.compiler.types.TextRule;
import souther.runtime.ConstraintViolation;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A {@code String} is a sequence of Unicode scalar values (spec §string-code-points), so text
 * holding half of a surrogate pair is refused at every door text comes in by.
 *
 * <p>The doors differ in how they say no and not in what they refuse. A derived decoder reports an
 * issue at the path, with the same code whether it was generated or is the one {@code souther run}
 * reads with; a crossing from Java aborts; a literal is a diagnostic; a pattern writing one is a
 * diagnostic. Beside each refusal, the same door takes a well-formed pair, so what is refused is the
 * half and not the character past the basic plane.
 */
class TextHoldingHalfASurrogatePairIsRefusedAtEveryDoorTest {

    private static final String HIGH = String.valueOf((char) 0xD800);
    private static final String LOW = String.valueOf((char) 0xDC00);
    private static final String PAIR = new String(Character.toChars(0x10000));

    /** Text each holding half a pair somewhere: alone, the wrong way round, and at the end. */
    private static final List<String> HALVES = List.of(HIGH, LOW, LOW + HIGH, "a" + HIGH, HIGH + "a");

    private static final String MODULE = """
            module demo

            data Code = String
            data V = { s: String, codes: List<Code>, m: Map<String, Int> }
            """;

    private static ClassLoader loaded(String source) throws Exception {
        return new BytesClassLoader(Compiler.compile(source),
                TextHoldingHalfASurrogatePairIsRefusedAtEveryDoorTest.class.getClassLoader());
    }

    private static Map<String, Object> v(String s, String code, String key) {
        return Map.of("s", s, "codes", List.of(code), "m", Map.of(key, 1L));
    }

    @Test
    void aDerivedDecoderRefusesItAtThePath() throws Exception {
        ClassLoader loader = loaded(MODULE);
        assertInstanceOf(Ok.class,
                Codecs.decoder(loader, "demo.V").decode(v(PAIR, PAIR, PAIR), Path.ROOT));
        for (String half : HALVES) {
            assertRefusedAt("/s", Codecs.decoder(loader, "demo.V").decode(v(half, "a", "a"),
                    Path.ROOT));
            assertRefusedAt("/codes/0", Codecs.decoder(loader, "demo.V").decode(v("a", half, "a"),
                    Path.ROOT));
            assertRefusedAt("/m/" + half, Codecs.decoder(loader, "demo.V").decode(v("a", "a", half),
                    Path.ROOT));
            assertRefusedAt("", Codecs.decoder(loader, "demo.Code").decode(half, Path.ROOT));
        }
    }

    private static void assertRefusedAt(String pointer, Result<?> result) {
        Issue issue = assertInstanceOf(Err.class, result).issues().asList().get(0);
        assertEquals(TextRule.REFUSED, issue.code());
        assertEquals(pointer, issue.path().toJsonPointer());
    }

    private static final String TAKING = """
            module demo

            data In = { s: String }
            data Out = Int

            behavior field : (i: In) -> Out constructs Out
            let field (i) = Out(String.length(i.s))

            behavior bare : (s: String) -> Out constructs Out
            let bare (s) = Out(String.length(s))

            behavior keyed : (m: Map<String, Int>) -> Out constructs Out
            let keyed (m) = Out(Map.size(m))
            """;

    /**
     * The reading {@code souther run} does refuses it the same way: a data's generated JSON decoder,
     * a {@code String} read on its own, and a map's key, which the generated decoder does not read.
     */
    @Test
    void theRunnersReadingRefusesItTheSameWay() throws Exception {
        String escapedHigh = "\\ud800";
        for (String[] each : new String[][] {
                {"field", "{\"s\": \"" + escapedHigh + "\"}", "/s"},
                {"bare", "\"" + escapedHigh + "\"", ""},
                {"keyed", "{\"" + escapedHigh + "\": 1}", "/" + HIGH}}) {
            JsonBoundary.Read.Refused refused = Crossing.refusalOf(TAKING, "demo", each[0], each[1]);
            Issue issue = refused.issues().asList().get(0);
            assertEquals(TextRule.REFUSED, issue.code(), each[0]);
            assertEquals(each[2], issue.path().toJsonPointer(), each[0]);
        }
        assertEquals("1", Crossing.of(TAKING, "demo", "bare", "\"\\ud800\\udc00\""));
    }

    private static final String IDENTITY = """
            module demo

            data In = { s: String }

            behavior identity : (s: String) -> String
            let identity (s) = s
            """;

    /** A Java caller handing a behavior or a constructor such text aborts the crossing. */
    @Test
    void aCrossingFromJavaAbortsOnIt() throws Exception {
        ClassLoader loader = loaded(IDENTITY);
        Object identity = Emitted.behavior(loader, "demo", "identity").getConstructor().newInstance();
        assertEquals(PAIR, Codecs.apply(identity, PAIR));
        for (String half : HALVES) {
            assertThrows(ConstraintViolation.class, () -> Codecs.apply(identity, half));
        }

        Constructor<?> in = loader.loadClass("demo.In").getDeclaredConstructor(String.class);
        in.setAccessible(true);
        in.newInstance(PAIR);
        for (String half : HALVES) {
            InvocationTargetException thrown =
                    assertThrows(InvocationTargetException.class, () -> in.newInstance(half));
            assertInstanceOf(ConstraintViolation.class, thrown.getCause());
        }
    }

    /** A literal holding one is refused where it is read. No escape writes one, so the text a
     *  compiler was handed is what holds it. */
    @Test
    void aLiteralHoldingItIsRefused() throws Exception {
        String written = """
                module demo

                let text: String = "%s"
                """;
        loaded(written.formatted(PAIR));
        for (String half : HALVES) {
            CompileException refused = assertThrows(CompileException.class,
                    () -> Compiler.compile(written.formatted(half)));
            assertInstanceOf(ParseMessage.AStringLiteralHoldsHalfASurrogatePair.class,
                    refused.diagnostic().said());
        }
    }

    /**
     * A pattern writing one is refused, wherever in the pattern it is written; one quoting the six
     * characters, or writing the pair as two escapes, is not.
     */
    @Test
    void aPatternWritingItIsRefused() throws Exception {
        String written = """
                module demo

                data V = String
                    invariant String.matches("%s", value)
                """;
        for (String pattern : List.of("\\\\uD800", "a\\\\x{DC00}", "[\\\\uD800-\\\\uDFFF]",
                "(?=a)a\\\\uDC00", "\\\\N{HIGH SURROGATES D800}")) {
            CompileException refused = assertThrows(CompileException.class,
                    () -> Compiler.compile(written.formatted(pattern)), pattern);
            assertInstanceOf(TypeMessage.ThePatternWritesHalfASurrogatePair.class,
                    refused.diagnostic().said(), pattern);
        }
        for (String pattern : List.of("\\\\uD800\\\\uDC00", "\\\\Q\\\\uD800\\\\E",
                "\\\\\\\\uD800", "[\\\\uD7FF-\\\\uE000]")) {
            loaded(written.formatted(pattern));
        }
    }
}
