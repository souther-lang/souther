package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.CodePoints;

import souther.compiler.evaluate.BoundUnderEvaluation;
import souther.compiler.regex.CodeMap;
import souther.compiler.semantics.CaseMapping;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A case conversion is read as a map on code points only over the strings it is exactly that for,
 * and over those it converts a string as the run time converts it.
 *
 * <p>The run time answers the full Unicode mapping of a text and then its Normalization Form C, so
 * a code point can become several, what a conversion makes of a code point can turn on what stands
 * beside it (the capital sigma that closes a word), and a letter followed by a combining mark can
 * compose into one letter. A string of stable starters each sent to one stable starter is none of
 * those, whichever ones stand beside it; and the code points a conversion answers are, for any
 * string, ones it answers as they stand. This asks both of the run time's own answer, for the
 * conversions a model can write — one, and one of the other — rather than reasoning them from the
 * way the map was worked out.
 */
class AStringACaseMapIsExactOnConvertsAsTheRunTimeConvertsItTest {

    private static final CaseMapping LOWER_OF_UPPER = new CaseMapping.Lowercase(
            CaseMapping.UPPERCASE);
    private static final CaseMapping UPPER_OF_LOWER = new CaseMapping.Uppercase(
            CaseMapping.LOWERCASE);

    private static final List<CaseMapping> CONVERSIONS = List.of(
            CaseMapping.LOWERCASE, CaseMapping.UPPERCASE, LOWER_OF_UPPER, UPPER_OF_LOWER);

    /**
     * Code points a conversion treats specially: a letter that closes a word, ones that become
     * several, ones a combining mark composes with, ones Hangul syllables are made of, ones with a
     * case of their own and ones whose case is another letter's.
     */
    private static final int[] SPECIAL = {
        0x03A3, 0x03C3, 0x03C2, 0x0130, 0x0131, 0x00DF, 0x1E9E, 0x0149, 0x01F0, 0x0390, 0x03B0,
        0xFB01, 0xFB03, 0xFB06, 0x0345, 0x0301, 0x030A, 0x0308, 0x0307, 0x1100, 0x1161, 0x11A8,
        0xAC00, 0x1C90, 0x10D0, 0x13A0, 0xAB70, 0x10400, 0x10428, 0x212A, 0x212B, 0x2126,
        0x01C4, 0x01C5, 0x01C6, 0x1F80, 0x1FB3, 0x1FBC, 'A', 'a', 'z', 'Z', 'i', 'I', 'k', 'K',
        ' ', '.', '0', '-'};

    private static CodeMap mapOf(CaseMapping conversion) {
        return CaseMaps.of(conversion);
    }

    private static String converted(CaseMapping conversion, String text) {
        String out = BoundUnderEvaluation.mapped(conversion, text);
        assertTrue(out != null, () -> "the run time answers " + text);
        return out;
    }

    /** What the map sends {@code codePoint} to, or -1 where it sends it nowhere. */
    private static int sentTo(CodeMap map, int codePoint) {
        List<CodePoints.Range> image = map.image(new CodePoints(
                List.of(new CodePoints.Range(codePoint, codePoint)))).ranges();
        if (image.isEmpty()) {
            return -1;
        }
        assertEquals(1, image.size(), "one code point goes to one");
        assertEquals(image.getFirst().from(), image.getFirst().to(), "to a single one");
        return image.getFirst().from();
    }

    private static boolean inDomain(CodeMap map, int codePoint) {
        return map.domain().has(codePoint);
    }

    /** A code point to build a string of: the special ones, or one the conversion moves. */
    private static int[] pool(CodeMap map) {
        List<Integer> out = new ArrayList<>();
        for (int each : SPECIAL) {
            out.add(each);
        }
        for (CodePoints.Range range : map.domain().ranges()) {
            for (int codePoint = range.from(); codePoint <= range.to(); codePoint += 83) {
                out.add(codePoint);
            }
        }
        for (int codePoint = 0; codePoint <= 0x1FFFF; codePoint++) {
            if (!Character.isSurrogate((char) codePoint) && codePoint <= Character.MAX_CODE_POINT
                    && (Character.toLowerCase(codePoint) != codePoint
                    || Character.toUpperCase(codePoint) != codePoint)) {
                out.add(codePoint);
            }
        }
        return out.stream().mapToInt(Integer::intValue).filter(
                codePoint -> !(codePoint >= 0xD800 && codePoint <= 0xDFFF)).toArray();
    }

    @Test
    void aStringOfTheDomainIsConvertedAsTheMapSendsItsCodePoints() {
        Random random = new Random(2769);
        List<String> wrong = new ArrayList<>();
        for (CaseMapping conversion : CONVERSIONS) {
            CodeMap map = mapOf(conversion);
            int[] pool = pool(map);
            int held = 0;
            for (int round = 0; round < 8000; round++) {
                int length = 1 + random.nextInt(7);
                StringBuilder text = new StringBuilder();
                StringBuilder expected = new StringBuilder();
                boolean every = true;
                for (int at = 0; at < length; at++) {
                    int codePoint = pool[random.nextInt(pool.length)];
                    text.appendCodePoint(codePoint);
                    if (inDomain(map, codePoint)) {
                        expected.appendCodePoint(sentTo(map, codePoint));
                    } else {
                        every = false;
                    }
                }
                String converted = converted(conversion, text.toString());
                if (every) {
                    held++;
                    if (!expected.toString().equals(converted)) {
                        wrong.add(conversion + " of " + escaped(text.toString()) + " is "
                                + escaped(converted) + ", not " + escaped(expected.toString()));
                    }
                }
                // Whatever the string, what comes of it is code points the conversion leaves be.
                converted.codePoints().filter(codePoint -> !map.leftAlone().has(codePoint))
                        .forEach(codePoint -> wrong.add(conversion + " of "
                                + escaped(text.toString()) + " answers "
                                + Integer.toHexString(codePoint) + ", which it does not leave be"));
            }
            int shown = held;
            assertTrue(held > 500, () -> "the strings of the domain were asked: " + shown);
        }
        assertEquals(List.of(), wrong.stream().distinct().limit(8).toList());
    }

    /**
     * What stands beside a code point of the domain does not change what it is sent to: asked of
     * the code points the conversion moves and one in every so many others, beside the ones that
     * decide a conversion, and beside one another.
     */
    @Test
    void whatStandsBesideACodePointOfTheDomainDoesNotChangeWhatItIsSentTo() {
        int[] beside = {'a', 'A', 'i', 0x03C3, 0x03C2, 0x0131, 0x10428, 0x1C90, 'k'};
        for (CaseMapping conversion : CONVERSIONS) {
            CodeMap map = mapOf(conversion);
            List<Integer> asked = new ArrayList<>();
            for (CodePoints.Range range : map.domain().ranges()) {
                for (int codePoint = range.from(); codePoint <= range.to(); codePoint += 61) {
                    asked.add(codePoint);
                }
            }
            for (int codePoint = 0; codePoint <= 0x1FFFF; codePoint++) {
                if ((Character.toLowerCase(codePoint) != codePoint
                        || Character.toUpperCase(codePoint) != codePoint)
                        && inDomain(map, codePoint)) {
                    asked.add(codePoint);
                }
            }
            for (int codePoint : asked) {
                String there = Character.toString(sentTo(map, codePoint));
                String own = Character.toString(codePoint);
                for (int next : beside) {
                    if (!inDomain(map, next)) {
                        continue;
                    }
                    String other = Character.toString(sentTo(map, next));
                    String nextOwn = Character.toString(next);
                    assertEquals(other + there, converted(conversion, nextOwn + own),
                            () -> conversion + " of " + escaped(nextOwn + own));
                    assertEquals(there + other, converted(conversion, own + nextOwn),
                            () -> conversion + " of " + escaped(own + nextOwn));
                    assertEquals(other + there + other,
                            converted(conversion, nextOwn + own + nextOwn),
                            () -> conversion + " of " + escaped(nextOwn + own + nextOwn));
                }
            }
        }
    }

    /** The capital sigma that closes a word is lowercased as one that does not, which depends on
     *  what stands beside it, so it is no part of the domain. */
    @Test
    void theCapitalSigmaThatClosesAWordIsOutsideTheLowercaseMap() {
        CodeMap lower = mapOf(CaseMapping.LOWERCASE);
        assertEquals("aς", converted(CaseMapping.LOWERCASE, "aΣ"));
        assertEquals("σ", converted(CaseMapping.LOWERCASE, "Σ"));
        assertFalse(inDomain(lower, 0x03A3));
        assertTrue(inDomain(lower, 0x03C3));
        assertTrue(inDomain(lower, 0x03C2));
        // And so is every conversion that has it among its steps.
        assertFalse(inDomain(mapOf(LOWER_OF_UPPER), 0x03A3));
    }

    /** A code point that becomes several, and one a combining mark composes with, are no part of
     *  the domain either: the answer is not one code point for each one handed. */
    @Test
    void aCodePointThatBecomesSeveralOrComposesIsOutsideTheMap() {
        CodeMap upper = mapOf(CaseMapping.UPPERCASE);
        CodeMap lower = mapOf(CaseMapping.LOWERCASE);
        assertEquals("SS", converted(CaseMapping.UPPERCASE, "ß"));
        assertEquals("FI", converted(CaseMapping.UPPERCASE, "ﬁ"));
        assertEquals("i̇", converted(CaseMapping.LOWERCASE, "İ"));
        for (int codePoint : new int[] {0x00DF, 0xFB01, 0x0149, 0x01F0}) {
            assertFalse(inDomain(upper, codePoint), () -> "U+" + Integer.toHexString(codePoint));
        }
        assertFalse(inDomain(lower, 0x0130));
        // A combining mark is no starter, and the letter it composes with is changed by it.
        assertFalse(inDomain(lower, 0x0301));
        assertFalse(inDomain(upper, 0x030A));
        assertEquals("Å", converted(CaseMapping.UPPERCASE, "å"));
    }

    /**
     * What a conversion answers it answers again as it stands: every code point of what it makes
     * of any one code point is one it leaves be, which is what is said of the strings it is not
     * exactly a map on.
     */
    @Test
    void whatAConversionAnswersOfACodePointIsLeftBeByIt() {
        List<String> notLeftBe = new ArrayList<>();
        for (int codePoint = 0; codePoint <= Character.MAX_CODE_POINT; codePoint++) {
            if (codePoint >= 0xD800 && codePoint <= 0xDFFF) {
                continue;
            }
            String text = Character.toString(codePoint);
            for (CaseMapping conversion : List.of(CaseMapping.LOWERCASE, CaseMapping.UPPERCASE)) {
                String out = converted(conversion, text);
                CodeMap map = mapOf(conversion);
                for (int answered : out.codePoints().toArray()) {
                    if (!map.leftAlone().has(answered) && notLeftBe.size() < 8) {
                        notLeftBe.add(conversion + " of U+" + Integer.toHexString(codePoint)
                                + " answers U+" + Integer.toHexString(answered));
                    }
                }
            }
        }
        assertEquals(List.of(), notLeftBe);
    }

    private static String escaped(String text) {
        StringBuilder out = new StringBuilder();
        text.codePoints().forEach(codePoint -> out.append(
                codePoint < 0x80 && codePoint >= 0x20 ? Character.toString(codePoint)
                        : "\\u{" + Integer.toHexString(codePoint) + "}"));
        return out.toString();
    }
}
