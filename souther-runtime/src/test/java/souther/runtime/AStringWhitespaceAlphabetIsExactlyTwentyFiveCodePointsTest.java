package souther.runtime;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.List;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Exhaustive counterpart to {@code AStringHasOneWhitespaceAlphabetTest} (souther-compiler), which
 * picks a handful of code points to tell String whitespace apart from three near-miss candidates.
 * Spec §string-whitespace enumerates a closed 25-code-point set, so membership in it is checked
 * exactly rather than sampled — a range boundary {@code Strings.isWhitespace} got wrong (dropping
 * U+0085, mistyping U+202F, or widening U+2000-U+200A past its edges) would pass a witness test
 * built only from the handful of code points issue #1871 named, and does not pass this one.
 */
class AStringWhitespaceAlphabetIsExactlyTwentyFiveCodePointsTest {

    /** The 25 code points spec §string-whitespace enumerates, written out rather than generated,
     *  so this test and the spec table can be read side by side. */
    private static final int[] MEMBERS = {
        0x0009, 0x000A, 0x000B, 0x000C, 0x000D,
        0x0020,
        0x0085,
        0x00A0,
        0x1680,
        0x2000, 0x2001, 0x2002, 0x2003, 0x2004, 0x2005, 0x2006, 0x2007, 0x2008, 0x2009, 0x200A,
        0x2028, 0x2029,
        0x202F,
        0x205F,
        0x3000,
    };

    /** Code points a boundary typo would most plausibly let through: the edges of every named
     *  range, one step outside each end, plus the "looks like whitespace" characters issue #1871's
     *  own witness test already distinguishes. */
    private static final int[] NON_MEMBERS = {
        0x0008, 0x000E,             // one below/above the TAB..CR run
        0x001C, 0x0007,             // C0 controls the old String.trim wrongly crossed
        0x001F, 0x0021,             // one below/above SPACE
        0x0084, 0x0086,             // one below/above NEL
        0x009F, 0x00A1,             // one below/above NBSP
        0x167F, 0x1681,             // one below/above OGHAM SPACE MARK
        0x1FFF, 0x200B,             // one below the 2000..200A run, and ZERO WIDTH SPACE just above it
        0x2027, 0x202A,             // one below LINE SEPARATOR, and one above PARAGRAPH SEPARATOR
        0x202E, 0x2030,             // one below/above NARROW NBSP
        0x205E, 0x2060,             // one below MEDIUM MATHEMATICAL SPACE, and WORD JOINER above it
        0x2FFF, 0x3001,             // one below/above IDEOGRAPHIC SPACE
        0xFEFF,                     // byte-order mark
    };

    @ParameterizedTest
    @MethodSource("members")
    void aMemberOfTheSpecsSetIsStrippedByTrimAndSplitByWords(int cp) {
        String ch = new String(Character.toChars(cp));
        assertEquals("a", Strings.trim(ch + "a" + ch), "trim should strip U+%04X".formatted(cp));
        assertEquals(List.of("a", "b"), Strings.words("a" + ch + "b"),
                "words should split on U+%04X".formatted(cp));
    }

    @ParameterizedTest
    @MethodSource("nonMembers")
    void aCodePointOutsideTheSpecsSetIsLeftAloneByBoth(int cp) {
        String ch = new String(Character.toChars(cp));
        String padded = ch + "a" + ch;
        assertEquals(padded, Strings.trim(padded), "trim should not strip U+%04X".formatted(cp));
        assertEquals(List.of("a" + ch + "b"), Strings.words("a" + ch + "b"),
                "words should not split on U+%04X".formatted(cp));
    }

    private static IntStream members() {
        return IntStream.of(MEMBERS);
    }

    private static IntStream nonMembers() {
        return IntStream.of(NON_MEMBERS);
    }
}
