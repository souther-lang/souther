package souther.compiler;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;

import org.junit.jupiter.api.Test;

import net.unit8.raoh.Issue;

import java.text.Normalizer;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Text that came from outside is canonicalized to NFC before anything reads it.
 *
 * <p>Unicode calls two forms of the same characters canonically equivalent — {@code が} as one code
 * point and as か plus a combining mark are the same text. Souther compares strings by their code
 * units, so without canonicalizing, the same name typed on two machines is two values: two `Map`
 * keys, two `Set` members, `==` false, and a length bound that depends on the sender's keyboard.
 * macOS filenames, some clipboard paths and some IMEs deliver the decomposed form.
 *
 * <p>The fix is that values are canonical, not that comparison ignores the difference. Ignoring it in
 * the comparison would leave `String.length` seeing something a comparison does not, which is a worse
 * incoherence than the one it closes. So the two places text arrives — a decoder, and a literal in a
 * source file — canonicalize, and everything downstream is ordinary code-unit comparison.
 *
 * <p>NFC and not NFKC: compatibility folding turns ① into 1 and a half-width kana into a full-width
 * one, which is a different claim than "these are the same characters".
 */
class AStringIsCanonicalAtTheBoundaryTest {

    /** か + a combining voiced sound mark: two code points, reading as one kana. Written as
     *  escapes because the two forms are the same glyph and an editor would silently pick one. */
    private static final String GA_NFD = "\u304b\u3099";
    /** The same kana as one code point. */
    private static final String GA_NFC = "\u304c";
    /** 葛 followed by a variation selector: normalization-stable, so it stays two code points. */
    private static final String VARIANT = "\u845b\udb40\udd01";

    private static final String MODULE = """
            module demo

            data In = { s: String }
            data Out = Int

            behavior calc : (i: In) -> Out constructs Out

            let calc (i) = Out(%s)
            """;

    private static long number(String expr, String input) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(MODULE.formatted(expr)),
                AStringIsCanonicalAtTheBoundaryTest.class.getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("s", input));
        Object behavior = loader.loadClass("demo.Calc$Impl").getDeclaredConstructor().newInstance();
        return (long) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
    }

    @Test
    void theTwoFormsAreDifferentStringsToTheJvm() {
        // The premise. If these were equal there would be nothing to fix, and the rest of this class
        // would pass without the boundary doing anything.
        assertNotEquals(GA_NFD, GA_NFC);
        assertEquals(2, GA_NFD.codePointCount(0, GA_NFD.length()));
        assertEquals(1, GA_NFC.codePointCount(0, GA_NFC.length()));
        assertEquals(GA_NFC, Normalizer.normalize(GA_NFD, Normalizer.Form.NFC));
    }

    @Test
    void aDecomposedValueArrivesComposed() throws Exception {
        assertEquals(1L, number("String.length(i.s)", GA_NFD),
                "the decomposed form is one character once it is through the boundary");
        assertEquals(1L, number("String.length(i.s)", GA_NFC));
    }

    @Test
    void bothFormsBecomeTheSameValue() throws Exception {
        // Equality is the point, not length. A domain that keys a Map or a Set by this text gets one
        // entry rather than two.
        String expr = "if i.s == \"" + GA_NFC + "\" then 1 else 0";
        assertEquals(1L, number(expr, GA_NFD), "a decomposed input equals the composed literal");
        assertEquals(1L, number(expr, GA_NFC));
    }

    @Test
    void aLengthBoundNoLongerDependsOnTheSendersKeyboard() throws Exception {
        ClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data V = String
                    invariant String.length(value) <= 1
                """), getClass().getClassLoader());
        Decoder<Object, ?> dec = Codecs.decoder(loader, "demo.V");

        assertTrue(dec.decode(GA_NFC, Path.ROOT) instanceof Ok, "composed: one character");
        assertTrue(dec.decode(GA_NFD, Path.ROOT) instanceof Ok,
                "decomposed: the same one character, so the same answer");
    }

    @Test
    void aPatternInvariantSeesTheCanonicalForm() throws Exception {
        // The pattern is written in a source literal and the value comes from a decoder. Both are
        // canonicalized, so the two meet in one form whichever way each was typed.
        ClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data V = String
                    invariant String.matches("%s+", value)
                """.formatted(GA_NFC)), getClass().getClassLoader());
        Decoder<Object, ?> dec = Codecs.decoder(loader, "demo.V");

        assertTrue(dec.decode(GA_NFD, Path.ROOT) instanceof Ok,
                "a decomposed value matches a pattern written composed");
        assertTrue(dec.decode(GA_NFC, Path.ROOT) instanceof Ok);
        assertTrue(dec.decode("\u304b", Path.ROOT) instanceof Err,
                "and か, which is a different character, still fails");
    }

    @Test
    void aSourceLiteralIsCanonicalWhicheverFormItWasTypedIn() throws Exception {
        // The literal below is written decomposed. Nothing in the language lets an author see which
        // form their editor wrote, so the compiler settles it rather than leaving it to the file.
        assertEquals(1L, number("String.length(\"" + GA_NFD + "\")", "x"),
                "a decomposed literal is one character to the compiler that read it");
    }

    @Test
    void aMapKeyIsCanonicalToo() throws Exception {
        // The keys of a decoded map do not pass the string leaf that canonicalizes — they are
        // whatever the object carried — so they are remapped after decoding. Without that,
        // Map<String, V> was the one place a boundary handed the domain text it had not
        // canonicalized, and Map.get with a literal missed a key written the other way.
        String src = """
                module demo

                data In = { m: Map<String, Int> }
                data Out = Int

                behavior calc : (i: In) -> Out constructs Out

                let calc (i) = Out(Map.get("%s", i.m) |> Option.withDefault(-1))
                """.formatted(GA_NFC);
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src),
                AStringIsCanonicalAtTheBoundaryTest.class.getClassLoader());
        Object behavior = loader.loadClass("demo.Calc$Impl").getDeclaredConstructor().newInstance();

        for (String key : new String[] {GA_NFC, GA_NFD}) {
            Object in = Codecs.decoded(loader, "demo.In", Map.of("m", Map.of(key, 7L)));
            assertEquals(7L, Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in)),
                    "a key written as " + key.length() + " UTF-16 units is found by the same literal");
        }
    }

    @Test
    void twoKeysThatCanonicalizeTogetherAreADecodeFailure() throws Exception {
        // A Set may collapse them — canonically equivalent text is one element — but a map would lose
        // the first key's value to the second with nothing said. So it fails at the key.
        ClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data V = { m: Map<String, Int> }
                """), getClass().getClassLoader());

        Map<String, Object> both = new LinkedHashMap<>();
        both.put(GA_NFC, 1L);
        both.put(GA_NFD, 2L);
        Result<?> r = Codecs.decoder(loader, "demo.V").decode(Map.of("m", both), Path.ROOT);

        assertTrue(r instanceof Err, "two keys, one text: the second value would replace the first");
        Issue issue = ((Err<?>) r).issues().asList().get(0);
        assertEquals("duplicate_key", issue.code());

        // One of them alone is fine, so the failure is the collision and not the character.
        assertTrue(Codecs.decoder(loader, "demo.V").decode(Map.of("m", Map.of(GA_NFD, 2L)), Path.ROOT)
                instanceof Ok);
    }

    @Test
    void whatNfcDoesNotJoinStaysApart() throws Exception {
        // A variation sequence is normalization-stable, so this is not a gap NFC closes and the
        // contract does not claim it does.
        assertEquals(2L, number("String.length(i.s)", VARIANT));
    }

    @Test
    void encodingBackGivesTheCanonicalForm() throws Exception {
        // The round trip is not the identity for a decomposed input — it is idempotent, and what
        // comes out is what the value is. Equal values write the same JSON, which is the law that
        // matters here.
        ClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data V = String
                """), getClass().getClassLoader());
        Result<?> decoded = Codecs.decoder(loader, "demo.V").decode(GA_NFD, Path.ROOT);
        assertTrue(decoded instanceof Ok);
        assertEquals(GA_NFC, Codecs.encode(loader, "demo.V", ((Ok<?>) decoded).value()));
    }
}
