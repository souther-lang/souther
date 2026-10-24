package souther.compiler.regex;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the code points of a format's strings of one length leave divided by a number, which code
 * points stand at an index of them, and which of those stand alike there, are what those strings
 * are.
 *
 * <p>The oracle is every string of the length over a few code points, each asked of the language
 * by {@link Language#has}: so a remainder the walk misses, a remainder it claims no string leaves,
 * and two code points it says stand alike where one string holding the first is a string and the
 * same holding the second is not, are each a difference from it. The formats are chosen so that
 * their code points go together — two indices holding one digit, a first letter choosing which
 * digits follow — since a walk taking the indices apart gets those wrong and a product of digits
 * right.
 */
class WhatAFormatsStringsLeaveIsReadOffThoseStringsTest {

    private static final int WORK = 1_000_000;
    private static final int[] ALPHABET = "0123ab".codePoints().toArray();

    private record Format(String regex, int length) {}

    private static final List<Format> FORMATS = List.of(
            new Format("[0-3]{3}", 3),
            new Format("(00|11|22)[0-2]", 3),
            new Format("a[0-1]{2}|b[2-3]{2}", 3),
            new Format("[0-2]*", 3),
            new Format("(ab|ba)[0-3]?", 2),
            new Format("(ab|ba)[0-3]?", 3));

    private static Language language(String regex) {
        Language made = PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning()).compile(new Meter(100_000,
                10_000_000, 1_000_000_000L));
        assertNotNull(made, regex);
        return made;
    }

    /** Every string of {@code length} over the alphabet the language holds. */
    private static List<int[]> strings(Language language, int length) {
        List<int[]> layer = new ArrayList<>(List.of(new int[0]));
        for (int at = 0; at < length; at++) {
            List<int[]> next = new ArrayList<>();
            for (int[] each : layer) {
                for (int symbol : ALPHABET) {
                    int[] longer = Arrays.copyOf(each, each.length + 1);
                    longer[each.length] = symbol;
                    next.add(longer);
                }
            }
            layer = next;
        }
        return layer.stream().filter(each -> language.has(new String(each, 0, each.length)))
                .toList();
    }

    private static BitSet leftBy(List<int[]> strings, Map<Integer, Long> weights, long shift,
                                 int divisor, Map<Integer, CodePoints> at) {
        BitSet out = new BitSet();
        for (int[] each : strings) {
            boolean held = at.entrySet().stream()
                    .allMatch(one -> one.getValue().has(each[one.getKey()]));
            if (!held) {
                continue;
            }
            long total = shift;
            for (int i = 0; i < each.length; i++) {
                total += weights.getOrDefault(i, 0L) * each[i];
            }
            out.set((int) Math.floorMod(total, (long) divisor));
        }
        return out;
    }

    @Test
    void theRemaindersLeftAreThoseTheStringsLeave() {
        List<Map<Integer, Long>> weighings = List.of(Map.of(0, 1L, 1, 1L, 2, 1L),
                Map.of(0, 3L, 2, -2L), Map.of(1, 5L), Map.of(0, 0L, 1, 7L, 2, 4L));
        for (Format format : FORMATS) {
            Language language = language(format.regex());
            List<int[]> strings = strings(language, format.length());
            for (Map<Integer, Long> weights : weighings) {
                for (int divisor : new int[] {1, 2, 5, 7}) {
                    for (long shift : new long[] {0, 3, -4}) {
                        assertEquals(leftBy(strings, weights, shift, divisor, Map.of()),
                                language.remaindersLeft(format.length(), weights, shift, divisor,
                                        Map.of(), WORK),
                                () -> format + " " + weights + " + " + shift + " by " + divisor);
                    }
                }
            }
        }
    }

    @Test
    void aCodePointHeldAtAnIndexIsHeldThereOnTheSameString() {
        Map<Integer, Long> weights = Map.of(0, 1L, 1, 2L, 2, 3L);
        for (Format format : FORMATS) {
            Language language = language(format.regex());
            List<int[]> strings = strings(language, format.length());
            for (int index = 0; index < format.length(); index++) {
                for (int symbol : ALPHABET) {
                    Map<Integer, CodePoints> at = Map.of(index, CodePoints.of(symbol));
                    int asked = index;
                    assertEquals(leftBy(strings, weights, 0, 7, at),
                            language.remaindersLeft(format.length(), weights, 0, 7, at, WORK),
                            () -> format + " holding " + Character.toString(symbol) + " at "
                                    + asked);
                }
            }
        }
    }

    @Test
    void theCodePointsAtAnIndexAreThoseTheStringsHoldThere() {
        for (Format format : FORMATS) {
            Language language = language(format.regex());
            List<int[]> strings = strings(language, format.length());
            for (int index = 0; index < format.length(); index++) {
                CodePoints held = CodePoints.NONE;
                for (int[] each : strings) {
                    held = held.or(CodePoints.of(each[index]));
                }
                int asked = index;
                assertEquals(held, language.codePointsAt(format.length(), index),
                        () -> format + " at " + asked);
            }
        }
    }

    /**
     * The sets a code point's values are taken apart into hold every one of them once, and two
     * code points of one set stand alike: a string holding the one at the index is held by the
     * language exactly where the same string holding the other is.
     */
    @Test
    void codePointsTakenAlikeStandAlike() {
        for (Format format : FORMATS) {
            Language language = language(format.regex());
            List<int[]> strings = strings(language, format.length());
            Set<String> held = new HashSet<>();
            strings.forEach(each -> held.add(new String(each, 0, each.length)));
            for (int index = 0; index < format.length(); index++) {
                CodePoints among = language.codePointsAt(format.length(), index);
                List<CodePoints> sets = language.alikeAt(format.length(), index, among);
                CodePoints all = CodePoints.NONE;
                for (CodePoints set : sets) {
                    assertFalse(set.isEmpty(), format::toString);
                    assertTrue(all.and(set).isEmpty(), () -> format + ": " + sets);
                    all = all.or(set);
                }
                assertEquals(among, all, format::toString);
                for (CodePoints set : sets) {
                    for (int[] each : strings) {
                        if (!set.has(each[index])) {
                            continue;
                        }
                        for (int other : ALPHABET) {
                            if (!set.has(other)) {
                                continue;
                            }
                            int[] swapped = each.clone();
                            swapped[index] = other;
                            String text = new String(swapped, 0, swapped.length);
                            assertTrue(held.contains(text), () -> format + ": " + sets
                                    + " holds " + Character.toString(other) + " beside "
                                    + new String(each, 0, each.length) + " and not " + text);
                        }
                    }
                }
            }
        }
    }

    /** Two code points that choose what follows them are taken apart, and the digits of a
     *  string of digits are not. */
    @Test
    void codePointsThatChooseWhatFollowsAreTakenApart() {
        Language chosen = language("a[0-1]{2}|b[2-3]{2}");
        assertEquals(2, chosen.alikeAt(3, 0, chosen.codePointsAt(3, 0)).size());
        Language digits = language("[0-3]{3}");
        assertEquals(1, digits.alikeAt(3, 1, digits.codePointsAt(3, 1)).size());
    }

    @Test
    void aWalkPastItsWorkSaysSo() {
        assertNull(language("[0-3]{3}").remaindersLeft(3, Map.of(0, 1L, 1, 1L, 2, 1L), 0, 7,
                Map.of(), 10));
    }
}
