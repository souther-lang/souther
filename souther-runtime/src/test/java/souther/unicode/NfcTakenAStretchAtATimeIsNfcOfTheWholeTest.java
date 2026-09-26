package souther.unicode;

import org.junit.jupiter.api.Test;

import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * {@code Normalization} normalizes a stretch at a time, cut before a code point nothing before it
 * can reach. That cut is right only if the NFC of every text is the stretches' NFC laid end to end,
 * so it is held against the text taken whole — the one-stretch answer — with the cut made as often
 * as it can be: before every code point it is allowed before.
 *
 * <p>The texts are drawn from the code points that decide where a cut may fall: starters and
 * composites, marks of several combining classes that reorder, starters that are the second of a
 * composition (Oriya, Kannada, Kaithi), Hangul jamo and syllables that compose by formula,
 * Tibetan marks whose decomposition begins with a mark, and marks outside the basic plane.
 */
class NfcTakenAStretchAtATimeIsNfcOfTheWholeTest {

    private static final int[] ALPHABET = {
            'a', 'e', 'u', 'A', 'c', ' ',
            0x00E9, 0x1E17, 0x01D6, 0x00C7, 0x1E09,             // composites with one and two marks
            0x0300, 0x0301, 0x0304, 0x0308, 0x0323, 0x0327, 0x0345, 0x031B,
            0x0B47, 0x0B3E, 0x0B56, 0x0B57,                     // Oriya: a starter second
            0x0CC6, 0x0CC2, 0x0CD5, 0x0CD6,                     // Kannada
            0x11099, 0x110BA, 0x1109A,                          // Kaithi, outside the basic plane
            0x1100, 0x1161, 0x11A8, 0x11AF, 0xAC00, 0xAC01,     // Hangul L, V, T, LV, LVT
            0x0F71, 0x0F72, 0x0F73, 0x0F80,                     // Tibetan
            0x1D165, 0x1D16E, 0x1D15E,                          // musical symbols
            0x0958, 0x2126};                                    // an exclusion, a singleton

    @Test
    void theStretchesLaidEndToEndAreTheWhole() {
        Random random = new Random(1980);
        for (int n = 0; n < 20000; n++) {
            StringBuilder text = new StringBuilder();
            int length = random.nextInt(24);
            for (int i = 0; i < length; i++) {
                text.appendCodePoint(ALPHABET[random.nextInt(ALPHABET.length)]);
            }
            String s = text.toString();
            assertEquals(Normalization.nfcWithin(s, Long.MAX_VALUE, Integer.MAX_VALUE),
                    Normalization.nfcWithin(s, Long.MAX_VALUE, 1),
                    () -> s.codePoints().mapToObj(Integer::toHexString).toList().toString());
        }
    }

    /** The bound is on the answer: exactly as long is an answer, one unit longer is none. */
    @Test
    void anAnswerLongerThanTheBoundIsNone() {
        String s = "é".repeat(5) + "𝅥";            // five é and a mark of two units
        assertEquals(7, Normalization.nfc(s).length());
        assertEquals(Normalization.nfc(s), Normalization.nfcWithin(s, 7, 1));
        assertNull(Normalization.nfcWithin(s, 6, 1));
        assertNull(Normalization.nfcWithin(s, 6));
    }
}
