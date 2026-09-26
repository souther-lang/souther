package souther.unicode;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * {@code Normalization.nfcWithin} answers text made only of code points below
 * {@code NFC_TRIVIAL_LIMIT} with the text itself, without running the algorithm. That is right only
 * where the algorithm would have answered the same, so the algorithm is run here over every such
 * code point and every pair of them.
 *
 * <p>The limit comes from Unicode's {@code NFC_Quick_Check}, and the algorithm is this repository's
 * own, so the two are held against each other rather than either being taken on the other's word.
 */
class TextBelowTheTrivialLimitIsItsOwnNfcTest {

    @Test
    void theAlgorithmLeavesEveryCodePointBelowTheLimitAndEveryPairOfThemAsTheyAre() {
        int limit = NormalizationTables.NFC_TRIVIAL_LIMIT;
        List<String> changed = new ArrayList<>();
        for (int first = 0; first < limit; first++) {
            String alone = Character.toString(first);
            if (!alone.equals(Normalization.normalizeWithin(alone, Long.MAX_VALUE))) {
                changed.add(Integer.toHexString(first));
            }
            for (int second = 0; second < limit; second++) {
                String pair = alone + Character.toString(second);
                if (!pair.equals(Normalization.normalizeWithin(pair, Long.MAX_VALUE))) {
                    changed.add(Integer.toHexString(first) + " " + Integer.toHexString(second));
                }
            }
        }
        assertEquals(List.of(), changed);
    }

    @Test
    void textBelowTheLimitIsAnsweredWithItself() {
        String latin = "Renée Ångström ˿";
        assertSame(latin, Normalization.nfc(latin));
    }

    /** U+02FF is the last code point that is answered without the algorithm; U+0300, the first that
     *  is not, changes the character before it. */
    @Test
    void theLimitFallsWhereACodePointFirstChangesWhatComesBeforeIt() {
        String last = "A˿";
        assertSame(last, Normalization.nfcWithin(last, Long.MAX_VALUE));
        assertEquals("À", Normalization.nfcWithin("À", Long.MAX_VALUE));
    }

    /** Text answered with itself is exactly as long as the answer, so its own length decides. */
    @Test
    void theBoundIsOnTheTextAnsweredWithItself() {
        String s = "abc";
        assertSame(s, Normalization.nfcWithin(s, 3));
        assertNull(Normalization.nfcWithin(s, 2));
    }
}
