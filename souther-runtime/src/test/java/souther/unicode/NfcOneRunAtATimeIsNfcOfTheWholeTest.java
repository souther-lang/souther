package souther.unicode;

import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.Random;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * {@code Normalization} settles one combining run at a time as it reads the text. That is right only
 * if the answer is what UAX #15's three steps give when each is taken over the whole text at once —
 * decompose everything, order every run of marks, compose left to right — so it is held against
 * those three steps, written out here as the standard states them.
 *
 * <p>The texts are drawn from the code points that decide where a run ends and what composes across
 * it: starters and composites, marks of several combining classes that reorder, starters that are
 * the second of a composition (Oriya, Kannada, Kaithi), Hangul jamo and syllables that compose by
 * formula, Tibetan marks that decompose, and marks outside the basic plane. Some texts hold runs of
 * more marks than are ordered by insertion, so the ordering by counting is read too.
 */
class NfcOneRunAtATimeIsNfcOfTheWholeTest {

    private static final int[] ALPHABET = {
            'a', 'e', 'u', 'A', 'c', ' ',
            0x00E9, 0x1E17, 0x01D6, 0x00C7, 0x1E09,             // composites with one and two marks
            0x0300, 0x0301, 0x0304, 0x0308, 0x0323, 0x0327, 0x0345, 0x031B,
            0x0B47, 0x0B3E, 0x0B56, 0x0B57,                     // Oriya: a starter second
            0x0CC6, 0x0CC2, 0x0CD5, 0x0CD6,                     // Kannada
            0x11099, 0x110BA, 0x1109A,                          // Kaithi, outside the basic plane
            0x1100, 0x1161, 0x11A8, 0x11AF, 0xAC00, 0xAC01,     // Hangul L, V, T, LV, LVT
            0x0F71, 0x0F72, 0x0F73, 0x0F80, 0x0344,             // marks that decompose
            0x1D165, 0x1D16E, 0x1D15E,                          // musical symbols
            0x0958, 0x2126, 0x16121};                           // an exclusion, a singleton, a second

    private static final int[] MARKS = {0x0300, 0x0301, 0x0323, 0x0327, 0x0345, 0x031B, 0x05B0};

    @Test
    void settlingARunAtATimeIsTheThreeStepsOverTheWhole() {
        Random random = new Random(1980);
        for (int n = 0; n < 20000; n++) {
            StringBuilder text = new StringBuilder();
            int length = random.nextInt(24);
            for (int i = 0; i < length; i++) {
                text.appendCodePoint(ALPHABET[random.nextInt(ALPHABET.length)]);
                if (random.nextInt(200) == 0) {
                    for (int m = random.nextInt(100); m > 0; m--) {
                        text.appendCodePoint(MARKS[random.nextInt(MARKS.length)]);
                    }
                }
            }
            String s = text.toString();
            assertEquals(threeStepsOverTheWhole(s), Normalization.nfc(s),
                    () -> s.codePoints().mapToObj(Integer::toHexString).toList().toString());
        }
    }

    /** The bound is on the answer: exactly as long is an answer, one unit longer is none. */
    @Test
    void anAnswerLongerThanTheBoundIsNone() {
        String s = "é".repeat(5) + "𝅥";            // five é and a mark of two units
        assertEquals(7, Normalization.nfc(s).length());
        assertEquals(Normalization.nfc(s), Normalization.nfcWithin(s, 7));
        assertNull(Normalization.nfcWithin(s, 6));
    }

    private static String threeStepsOverTheWhole(String s) {
        int[] decomposed = s.codePoints().flatMap(cp -> {
            int[] parts = Normalization.decomposeOne(cp);
            return parts == null ? IntStream.of(cp) : Arrays.stream(parts);
        }).toArray();
        for (int i = 1; i < decomposed.length; i++) {
            int markClass = Normalization.combiningClass(decomposed[i]);
            if (markClass == 0) {
                continue;
            }
            for (int j = i; j > 0 && Normalization.combiningClass(decomposed[j - 1]) > markClass; j--) {
                int t = decomposed[j - 1];
                decomposed[j - 1] = decomposed[j];
                decomposed[j] = t;
            }
        }
        int[] result = new int[decomposed.length];
        int length = 0;
        int starterAt = -1;
        int lastClass = -1;
        for (int cp : decomposed) {
            int cpClass = Normalization.combiningClass(cp);
            Integer composed = starterAt >= 0 && (lastClass < 0 || lastClass < cpClass)
                    ? Normalization.compose(result[starterAt], cp) : null;
            if (composed != null) {
                result[starterAt] = composed;
                continue;
            }
            result[length++] = cp;
            if (cpClass == 0) {
                starterAt = length - 1;
                lastClass = -1;
            } else {
                lastClass = cpClass;
            }
        }
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < length; i++) {
            out.appendCodePoint(result[i]);
        }
        return out.toString();
    }
}
