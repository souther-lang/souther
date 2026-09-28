package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@code trim} and {@code words} are both defined over one whitespace alphabet — the fixed
 * code-point set spec §string-whitespace enumerates — rather than each reaching for a different
 * platform notion of "blank" (issue #1871). The pairs below tell that alphabet apart from three
 * candidates it is not: {@code java.lang.String#trim}'s {@code <= U+0020}, {@code java.util.regex}'s
 * ASCII {@code \s} (the old {@code words}), and {@code Character#isWhitespace}, which excludes NBSP
 * and admits a control character below U+0020. Every expected value here is written by hand — this
 * is the specification's own contract, not a comparison against what a host method already answers.
 */
class AStringHasOneWhitespaceAlphabetTest {

    private static final String MODULE = """
            module demo

            import String ( trim, words )

            data In = String
            data Out = { trimmed: String, tokens: List<String> }

            behavior run : (i: In) -> Out constructs Out

            let run (i) = Out { trimmed = trim(i.value), tokens = words(i.value) }
            """;

    private static Map<?, ?> runOn(String text) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(MODULE),
                AStringHasOneWhitespaceAlphabetTest.class.getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", text);
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
    }

    @Test
    void aFullWidthIdeographicSpaceIsWhitespaceUnlikeAsciiOnlySplitting() throws Exception {
        assertEquals("a", runOn("　a　").get("trimmed"),
                "U+3000 is not in \\s, the ASCII class the old words() split on");
        assertEquals(List.of("会社名", "部署名"), runOn("会社名　部署名").get("tokens"));
    }

    @Test
    void aNoBreakSpaceIsWhitespaceUnlikeCharacterIsWhitespace() throws Exception {
        assertEquals("a", runOn(" a ").get("trimmed"),
                "Character.isWhitespace(0x00A0) is false; this alphabet disagrees with that method");
        assertEquals(List.of("a", "b"), runOn("a b").get("tokens"));
    }

    @Test
    void aFileSeparatorControlCharacterIsNotWhitespaceUnlikeTheOldJdkTrim() throws Exception {
        assertEquals("\u001Ca\u001C", runOn("\u001Ca\u001C").get("trimmed"),
                "java.lang.String#trim stripped U+001C as <= U+0020; this alphabet does not");
        assertEquals(List.of("a\u001Cb"), runOn("a\u001Cb").get("tokens"));
    }

    @Test
    void aBellControlCharacterIsNotWhitespaceEitherUnlikeTheOldJdkTrim() throws Exception {
        assertEquals("\u0007a\u0007", runOn("\u0007a\u0007").get("trimmed"));
    }

    @Test
    void aZeroWidthSpaceIsNotWhitespaceDespiteBeingInvisible() throws Exception {
        assertEquals(List.of("a​b"), runOn("a​b").get("tokens"),
                "invisible is not the same claim as whitespace");
    }

    @Test
    void aByteOrderMarkIsNotWhitespace() throws Exception {
        assertEquals(List.of("a﻿b"), runOn("a﻿b").get("tokens"));
    }

    @Test
    void wordsOfATrimmedStringIsWordsOfTheOriginal() throws Exception {
        String text = "  the  quick　fox  ";
        Map<?, ?> whole = runOn(text);
        Map<?, ?> trimmedOnly = runOn((String) whole.get("trimmed"));
        assertEquals(whole.get("tokens"), trimmedOnly.get("tokens"),
                "trim and words scan the same alphabet, so trimming first changes no word split");
    }
}
