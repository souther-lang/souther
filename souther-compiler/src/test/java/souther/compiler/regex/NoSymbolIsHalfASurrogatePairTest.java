package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A symbol is a Unicode scalar value, so nothing built here reads half of a surrogate pair.
 *
 * <p>A {@code String} holds no such half, and the sets a pattern is read into are sets of what a
 * {@code String} holds. The places a surrogate could come back in are the ones that make a set out
 * of everything else — the universe, a complement, {@code .}, a negated class, a run written across
 * the surrogates — and each is asked here.
 */
class NoSymbolIsHalfASurrogatePairTest {

    private static final int[] SURROGATES = {0xD800, 0xDBFF, 0xDC00, 0xDFFF};

    @Test
    void theUniverseHoldsNoSurrogate() {
        for (int each : SURROGATES) {
            assertFalse(CodePoints.EVERYTHING.has(each), Integer.toHexString(each));
        }
        assertEquals(0x110000L - 0x800L, CodePoints.EVERYTHING.size(),
                "every code point but the two thousand and forty-eight surrogates");
    }

    @Test
    void aComplementIsTakenWithinTheUniverse() {
        CodePoints some = CodePoints.of('a').or(CodePoints.between(0x10000, 0x10FFFF));
        for (CodePoints each : List.of(CodePoints.NONE.not(), some.not(), some.not().not())) {
            for (int surrogate : SURROGATES) {
                assertFalse(each.has(surrogate), each + " holds " + Integer.toHexString(surrogate));
            }
        }
        assertEquals(CodePoints.EVERYTHING, CodePoints.NONE.not());
        assertEquals(some, some.not().not());
    }

    @Test
    void aSurrogateIsNoSymbolToName() {
        assertThrows(IllegalArgumentException.class, () -> CodePoints.of(0xD800));
        assertThrows(IllegalArgumentException.class, () -> CodePoints.between(0xD800, 0xE000));
        assertThrows(IllegalArgumentException.class, () -> CodePoints.between(0xD7FF, 0xDFFF));
    }

    /**
     * A run written backwards is refused, and not read as holding nothing — including one whose
     * ends lie either side of the surrogates, which no range of scalar values contains.
     */
    @Test
    void aRunWrittenBackwardsIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> CodePoints.between(0xE000, 0xD7FF));
        assertThrows(IllegalArgumentException.class, () -> CodePoints.between('b', 'a'));
    }

    /** A run written across the surrogates holds the scalar values either side and no others. */
    @Test
    void aRunAcrossTheSurrogatesLeavesThemOut() {
        assertEquals(CodePoints.of(0xD7FF).or(CodePoints.of(0xE000)),
                CodePoints.between(0xD7FF, 0xE000));
        assertEquals(CodePoints.of(0xD7FF).or(CodePoints.of(0xE000)), heldBy("[\\uD7FF-\\uE000]"));
    }

    /** What a pattern makes of everything else holds no surrogate either. */
    @Test
    void whatAPatternMakesOfEverythingElseHoldsNoSurrogate() {
        for (String pattern : List.of(".", "[^a]", "\\D", "\\W", "\\S", "[^\\x{10000}-\\x{10FFFF}]")) {
            CodePoints held = heldBy(pattern);
            for (int surrogate : SURROGATES) {
                assertFalse(held.has(surrogate), pattern + " holds " + Integer.toHexString(surrogate));
            }
        }
    }

    /** And a machine accepts no text holding one, whatever the pattern. */
    @Test
    void noMachineAcceptsHalfAPair() {
        String high = String.valueOf((char) 0xD800);
        String low = String.valueOf((char) 0xDC00);
        for (String pattern : List.of(".", "[\\s\\S]*", "[^a]*", ".{1,2}")) {
            Language language = PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                    PatternParser.read(pattern)).meaning())
                    .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
            for (String text : List.of(high, low, low + high, "a" + high)) {
                assertFalse(language.has(text), pattern);
            }
            assertFalse(language.not(PatternPlan.Budget.OF_ADMITTED_VALUES.meter()).has(high),
                    "nor does what " + pattern + " leaves out");
        }
        assertFalse(Language.EVERY_STRING.has(high));
    }

    /**
     * An escape writing half of a pair is refused, and the escape is what is quoted.
     *
     * <p>The reader refuses it rather than naming a symbol that is not one. A pair written as two
     * escapes is one character, and a backslash that is itself escaped writes the characters after
     * it and not an escape.
     */
    @Test
    void anEscapeWritingHalfAPairIsRefusedAsItIsWritten() {
        Map<String, String> quoted = Map.of(
                "\\uD800", "\\uD800",
                "a\\uDC00", "\\uDC00",
                "\\x{D800}", "\\x{D800}",
                "[\\uD800-\\uDFFF]", "\\uD800",
                "\\uD83D\\x{DE00}", "\\uD83D");
        quoted.forEach((pattern, escape) -> {
            PatternRead.Refused refused =
                    assertInstanceOf(PatternRead.Refused.class, PatternParser.read(pattern), pattern);
            assertEquals(PatternRead.Refusal.A_CHARACTER_NO_STRING_HOLDS, refused.why(), pattern);
            assertEquals(escape, refused.construct(), pattern);
        });

        assertEquals(CodePoints.of(0x1F600), heldBy("\\uD83D\\uDE00"));
        assertEquals(PatternMeaning.text("\\uD800"),
                assertInstanceOf(PatternRead.Read.class, PatternParser.read("\\\\uD800")).meaning());
        assertEquals(CodePoints.between(0xD7FF, 0xE000), heldBy("[\\uD7FF-\\uE000]"));
    }

    private static CodePoints heldBy(String pattern) {
        return assertInstanceOf(PatternMeaning.Symbols.class,
                assertInstanceOf(PatternRead.Read.class, PatternParser.read(pattern)).meaning())
                .held();
    }
}
