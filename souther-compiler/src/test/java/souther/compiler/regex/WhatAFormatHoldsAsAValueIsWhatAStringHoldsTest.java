package souther.compiler.regex;

import java.time.Duration;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.Map;
import java.util.Random;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a format holds as a value is what a {@code String} holds: a sequence the format accepts and
 * Normalization Form C leaves as it is.
 *
 * <p>Held against every string over a small alphabet that has a letter, its precomposed form with
 * an acute, a digit and two combining marks, each a value only where the run time's NFC leaves it
 * as written. Every string the format holds as written is such a value, and what the code points
 * of those strings place and come to is placed and come to by values; over an alphabet of starters
 * nothing is lost.
 */
class WhatAFormatHoldsAsAValueIsWhatAStringHoldsTest {

    private static final int[] ALPHABET = {'a', 'b', '1', 0x300, 0x301, 0xE1};

    private static final List<String> FORMATS = List.of(
            "a\\x{301}|bb",
            "[ab][\\x{300}\\x{301}b1]",
            "a\\x{301}?b|1\\x{301}1",
            "[\\x{e1}a]\\x{301}?[1b]",
            "(1|a)(\\x{301}|1)[ab]");

    private static Language language(String regex) {
        Language made = PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning()).compile(METER);
        assertNotNull(made, regex);
        return made;
    }

    private static final Meter METER = new Meter(100_000, 10_000_000, 1_000_000_000L);

    /** Whether a {@code String} can be {@code text}: the run time holds a string as its NFC. */
    private static boolean aValue(Language format, String text) {
        return format.has(text) && Normalization.nfc(text).equals(text);
    }

    /** Every string of {@code length} over {@link #ALPHABET}. */
    private static List<String> stringsOf(int length) {
        List<String> out = new ArrayList<>(List.of(""));
        for (int at = 0; at < length; at++) {
            List<String> longer = new ArrayList<>();
            for (String each : out) {
                for (int cp : ALPHABET) {
                    longer.add(each + Character.toString(cp));
                }
            }
            out = longer;
        }
        return out;
    }

    /** The case the review met: a letter and a combining acute are one code point held, so the
     *  only string of two that is a value is {@code bb}. */
    @Test
    void aSequenceNormalizationChangesIsNoValueOfTheFormat() {
        Language format = language("a\\x{301}|bb");
        StringsHeldAsWritten held = format.heldAsWritten();
        assertTrue(format.codePointsAt(2, 0).has('a'), "the format places a letter first");
        assertEquals(CodePoints.of('b'), held.codePointsAt(2, 0));
        assertFalse(held.has("á"));
        assertTrue(held.has("bb"));
    }

    /**
     * Every string the format holds as written is a value, and what those strings place at an
     * index and leave of a weighed total is what values place and leave.
     */
    @Test
    void whatTheStringsHeldAsWrittenShowIsShownByValues() {
        for (String regex : FORMATS) {
            Language format = language(regex);
            StringsHeldAsWritten held = format.heldAsWritten();
            for (int length = 1; length <= 3; length++) {
                List<String> values = new ArrayList<>();
                for (String each : stringsOf(length)) {
                    if (held.has(each)) {
                        assertTrue(aValue(format, each), regex + " holds " + each.codePoints()
                                .mapToObj(Integer::toHexString).toList() + " as written");
                    }
                    if (aValue(format, each)) {
                        values.add(each);
                    }
                }
                for (int index = 0; index < length; index++) {
                    CodePoints placed = CodePoints.NONE;
                    for (String value : values) {
                        placed = placed.or(CodePoints.of(value.codePointAt(
                                value.offsetByCodePoints(0, index))));
                    }
                    assertTrue(held.codePointsAt(length, index).less(placed).isEmpty(),
                            regex + " places at " + index + " of " + length);
                }
                BitSet left = held.remaindersLeft(length, Map.of(0, 1L, 1, 2L), 0, 3, Map.of(),
                        1_000_000);
                BitSet reached = new BitSet();
                for (String value : values) {
                    int[] cps = value.codePoints().toArray();
                    long total = cps[0] + (cps.length > 1 ? 2L * cps[1] : 0);
                    reached.set((int) Math.floorMod(total, 3L));
                }
                BitSet beyond = (BitSet) left.clone();
                beyond.andNot(reached);
                assertTrue(beyond.isEmpty(), regex + " leaves " + left + " of " + length
                        + ", values " + reached);
            }
        }
    }

    /** Over code points every one of which is a starter nothing joins, nothing is lost. */
    @Test
    void overStartersTheFormatIsHeldWhole() {
        Language format = language("[ab1\\x{e1}]{1,3}");
        StringsHeldAsWritten held = format.heldAsWritten();
        for (int length = 1; length <= 3; length++) {
            for (String each : stringsOf(length)) {
                assertEquals(format.has(each), held.has(each), each);
            }
        }
    }

    /**
     * Nothing that joins the code point before it is a stable starter: every code point after the
     * first in what a composite decomposes to, the vowels and finals of Hangul among them. And a
     * string of stable starters is NFC, wherever they stand.
     */
    @Test
    void aStringOfStableStartersIsInNormalFormC() {
        CodePoints stable = StableStarters.all();
        for (int cp : new int[] {0x301, 0x300, 0x1161, 0x11A8, 0x3099}) {
            assertFalse(stable.has(cp), Integer.toHexString(cp));
        }
        for (int cp : new int[] {'a', 0xE1, 0x1100, 0x304B, 0x4E00}) {
            assertTrue(stable.has(cp), Integer.toHexString(cp));
        }
        List<int[]> ranges = new ArrayList<>();
        stable.ranges().forEach(range -> ranges.add(new int[] {range.from(), range.to()}));
        Random picking = new Random(2708);
        for (int tried = 0; tried < 20_000; tried++) {
            StringBuilder text = new StringBuilder();
            for (int at = 1 + picking.nextInt(5); at > 0; at--) {
                int[] range = ranges.get(picking.nextInt(ranges.size()));
                text.appendCodePoint(range[0] + picking.nextInt(range[1] - range[0] + 1));
            }
            String written = text.toString();
            assertEquals(written, Normalization.nfc(written), () -> written.codePoints()
                    .mapToObj(Integer::toHexString).toList().toString());
        }
    }

    /** A walk that would move more remainders than it was given stops, however far past the
     *  most an int counts the moves it would make come to. */
    @Test
    void aWalkPastItsWorkStopsHoweverMuchItWouldMove() {
        Language format = language("[\\x{0}-\\x{ffff}]{3}");
        assertTimeoutPreemptively(Duration.ofSeconds(10), () ->
                assertNull(format.remaindersLeft(3, Map.of(0, 1L, 1, 1L, 2, 1L), 0, 65_536,
                        Map.of(), Integer.MAX_VALUE)));
    }

    /** What a machine of many code points in a row comes to is worked out without a step for each
     *  of them on the call stack: a chain of digits, made as the machine of {@code [0-9]{n}} is
     *  without compiling the pattern. */
    @Test
    void theSumsOfALongFormatAreWorkedOutWhole() {
        int many = 50_000;
        List<List<Automaton.Step>> steps = new ArrayList<>();
        for (int state = 0; state < many; state++) {
            steps.add(List.of(new Automaton.Step(CodePoints.between('0', '9'), state + 1)));
        }
        steps.add(List.of());
        BitSet accepting = new BitSet();
        accepting.set(many);
        assertEquals(new Language.Ends(48L * many, 57L * many),
                CodePointSums.range(Automaton.madeOf(steps, accepting), CodePoints::least,
                        over -> over.ranges().getLast().to()));
    }
}
