package souther.compiler;

import souther.runtime.ConstraintViolation;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Every length, index and range the String library publishes counts Unicode code points. The JVM
 * stores a string in UTF-16 units, and a supplementary-plane character takes two of them, so the two
 * counts disagree exactly where a Japanese domain notices: {@code 𠮷田}, {@code 髙橋}, an emoji in a
 * remarks field. Before this, {@code length} counted units while {@code characters} and
 * {@code reverse} walked code points, so the operations did not agree with each other and
 * {@code slice} could answer half a surrogate pair.
 *
 * <p>These fix the contract by exercising the laws it makes true rather than the implementation:
 * lengths agree across the operations, a slice of the whole string is the string, padding reaches
 * the width it was asked for, and nothing produces a broken string.
 *
 * <p>Code point is not grapheme cluster. A base letter with a combining accent is two code points
 * and one character to a reader; a family emoji joined with ZWJ is several. That is stated, not
 * fixed: those units depend on Unicode segmentation and belong to a different function than
 * {@code length}.
 */
class AStringIsMeasuredInCodePointsTest {

    /** A supplementary-plane kanji: one code point, two UTF-16 units. */
    private static final String YOSHI = "𠮷";
    /** A base letter and a combining acute accent — two code points, and NFD, so a boundary
     *  canonicalizes it to the one composed code point. Written as escapes because the difference
     *  this test is about is invisible in the glyph. */
    private static final String DECOMPOSED = "e\u0301";
    /** 葛 followed by a variation selector: two code points, one character to a reader, and stable
     *  under every normalization form — so it stays two after a boundary. */
    private static final String VARIANT = "\u845b\udb40\udd01";
    /** A family emoji: several code points joined with zero-width joiners, one grapheme cluster. */
    private static final String FAMILY = "👨‍👩‍👧";

    private static final String MODULE = """
            module demo

            data In = { s: String }
            data Out = Int

            behavior calc : (i: In) -> Out constructs Out

            let calc (i) = Out(%s)
            """;

    private static final String TEXT_MODULE = """
            module demo

            data In = { s: String }
            data Out = String

            behavior calc : (i: In) -> Out constructs Out

            let calc (i) = Out(%s)
            """;

    private static long number(String expr, String input) throws Exception {
        return (long) run(MODULE, expr, input);
    }

    private static String text(String expr, String input) throws Exception {
        return (String) run(TEXT_MODULE, expr, input);
    }

    private static Object run(String module, String expr, String input) throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(module.formatted(expr)), getClass0());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("s", input));
        Object behavior = loader.loadClass("demo.Calc$Impl").getDeclaredConstructor().newInstance();
        return Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
    }

    private static ClassLoader getClass0() {
        return AStringIsMeasuredInCodePointsTest.class.getClassLoader();
    }

    @Test
    void lengthCountsCodePointsNotUtf16Units() throws Exception {
        assertEquals(3L, number("String.length(i.s)", "abc"));
        assertEquals(2L, number("String.length(i.s)", "髙橋"), "both are in the basic plane");
        assertEquals(1L, number("String.length(i.s)", YOSHI), "one character, two UTF-16 units");
        assertEquals(2L, number("String.length(i.s)", YOSHI + "田"));
        assertEquals(0L, number("String.length(i.s)", ""));
    }

    @Test
    void lengthAgreesWithBothSplits() throws Exception {
        for (String s : List.of("abc", "髙橋", YOSHI + "田", VARIANT, FAMILY, "")) {
            long length = number("String.length(i.s)", s);
            assertEquals(length, number("List.length(String.characters(i.s))", s),
                    "characters disagreed with length for " + s);
            assertEquals(length, number("List.length(String.codePoints(i.s))", s),
                    "codePoints disagreed with length for " + s);
        }
    }

    @Test
    void aSliceOfTheWholeStringIsTheString() throws Exception {
        // Every input here is already NFC, so what the boundary hands the domain is what was sent
        // and the law reads as written. The canonicalizing case has its own test.
        for (String s : List.of("abc", "髙橋", YOSHI + "田", VARIANT, FAMILY, "")) {
            assertEquals(s, text("String.slice(0, String.length(i.s), i.s)", s));
        }
    }

    @Test
    void sliceCutsBetweenCodePointsAndNeverInsideOne() throws Exception {
        assertEquals(YOSHI, text("String.slice(0, 1, i.s)", YOSHI + "田"),
                "the first character comes out whole, not as half a surrogate pair");
        assertEquals("田", text("String.slice(1, 2, i.s)", YOSHI + "田"));
        assertEquals("", text("String.slice(1, 1, i.s)", YOSHI + "田"), "an empty range is empty");
    }

    @Test
    void twoSlicesThatMeetJoinBackIntoTheWhole() throws Exception {
        String s = YOSHI + "田" + YOSHI;
        assertEquals(s, text("String.slice(0, 1, i.s) ++ String.slice(1, String.length(i.s), i.s)", s));
    }

    @Test
    void anIndexTheStringHasNotGotAborts() {
        assertThrows(ConstraintViolation.class, () -> number("String.length(String.slice(0, 5, i.s))", YOSHI));
        assertThrows(ConstraintViolation.class, () -> number("String.length(String.slice(-1, 1, i.s))", "abc"));
        assertThrows(ConstraintViolation.class, () -> number("String.length(String.slice(2, 1, i.s))", "abc"));
    }

    @Test
    void paddingReachesTheWidthItWasAskedForInCodePoints() throws Exception {
        assertEquals("0" + YOSHI, text("String.padLeft(2, \"0\", i.s)", YOSHI),
                "one code point wide, so one pad character is still needed");
        assertEquals(YOSHI + "0", text("String.padRight(2, \"0\", i.s)", YOSHI));
        assertEquals("00abc", text("String.padLeft(5, \"0\", i.s)", "abc"));
        assertEquals("abc", text("String.padLeft(2, \"0\", i.s)", "abc"), "already wide enough");
    }

    @Test
    void aMultiCodePointPadIsCutToTheWidthRatherThanOvershooting() throws Exception {
        assertEquals("ababX", text("String.padLeft(5, \"ab\", i.s)", "X"));
        assertEquals("abaX", text("String.padLeft(4, \"ab\", i.s)", "X"),
                "the last copy is cut, so the width is exact rather than a whole number of copies");
        assertEquals(YOSHI + YOSHI + "X", text("String.padLeft(3, \"" + YOSHI + "\", i.s)", "X"),
                "a supplementary-plane pad counts one per copy");
    }

    @Test
    void anEmptyPadFillsNothing() throws Exception {
        assertEquals("X", text("String.padLeft(5, \"\", i.s)", "X"),
                "nothing can be repeated into a width, so the string comes back as it was");
    }

    @Test
    void reverseTurnsTheCodePointsAroundAndKeepsEachWhole() throws Exception {
        assertEquals("B" + YOSHI + "A", text("String.reverse(i.s)", "A" + YOSHI + "B"));
        assertEquals(YOSHI, text("String.reverse(i.s)", YOSHI));
    }

    @Test
    void aGraphemeClusterIsNotACodePointAndTheContractSaysSo() throws Exception {
        // Stated rather than fixed: `length` counts code points, and a reader counts something else.
        // A caller who needs what a reader sees needs Unicode segmentation, which is a different
        // function than this one — the point here is that the answer is defined, not that it is one.
        // Both survive the boundary's canonicalization: no normalization form joins a variation
        // sequence or a ZWJ sequence, so this gap is not the one NFC closes.
        assertEquals(2L, number("String.length(i.s)", VARIANT), "a kanji and its variation selector");
        assertEquals(5L, number("String.length(i.s)", FAMILY), "three people and two joiners");
    }
}
