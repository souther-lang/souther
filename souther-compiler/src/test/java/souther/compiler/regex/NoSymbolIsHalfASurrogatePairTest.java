package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
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
                    PatternParser.read(pattern)).syntax())
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
     * Which escapes write half of a pair, read the way the engine reads them.
     *
     * <p>A pair written as two escapes is one character, and text that is quoted or whose backslash
     * is itself escaped writes the six characters and not a surrogate.
     */
    @Test
    void anEscapeWritingHalfAPairIsFoundWhereverItIsWritten() {
        assertEquals("\\uD800", PatternEscapes.firstWrittenSurrogate("\\uD800"));
        assertEquals("\\uDC00", PatternEscapes.firstWrittenSurrogate("a\\uDC00"));
        assertEquals("\\x{D800}", PatternEscapes.firstWrittenSurrogate("\\x{D800}"));
        assertEquals("\\uD800", PatternEscapes.firstWrittenSurrogate("[\\uD800-\\uDFFF]"));
        assertEquals("\\uD83D", PatternEscapes.firstWrittenSurrogate("\\uD83D\\x{DE00}"));
        assertEquals("\\N{HIGH SURROGATES D800}",
                PatternEscapes.firstWrittenSurrogate("\\N{HIGH SURROGATES D800}"));
        assertEquals("\\uDE00", PatternEscapes.firstWrittenSurrogate("(?=a)b\\uDE00"),
                "past a construct the subset does not read");

        assertNull(PatternEscapes.firstWrittenSurrogate("\\uD83D\\uDE00"));
        assertNull(PatternEscapes.firstWrittenSurrogate("\\Q\\uD800\\E"));
        assertNull(PatternEscapes.firstWrittenSurrogate("\\\\uD800"));
        assertNull(PatternEscapes.firstWrittenSurrogate("[\\uD7FF-\\uE000]"));
        assertNull(PatternEscapes.firstWrittenSurrogate("\\x{1F600}\\N{LATIN SMALL LETTER A}"));
    }

    /** The subset reader stops at one rather than naming a symbol that is not one. */
    @Test
    void theReaderStopsAtHalfAPair() {
        for (String pattern : List.of("\\uD800", "\\x{DC00}", "[\\uD800-\\uDFFF]")) {
            assertEquals(PatternRead.Unsupported.A_CHARACTER_NO_STRING_HOLDS,
                    assertInstanceOf(PatternRead.NotRead.class, PatternParser.read(pattern)).why(),
                    pattern);
        }
    }

    private static CodePoints heldBy(String pattern) {
        return assertInstanceOf(PatternSyntax.Symbols.class,
                assertInstanceOf(PatternRead.Read.class, PatternParser.read(pattern)).syntax())
                .held();
    }
}
