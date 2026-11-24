package souther.compiler.regex;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.pattern.CodePoints;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A code point a composite is composed of after another is no stable starter, even where it
 * decomposes itself and so stands in no full decomposition. Kirat Rai's U+16D68 is two of U+16D67,
 * and U+16D63 before it composes with it into U+16D6A; Tulu-Tigalari's and Gurung Khema's vowel
 * signs that decompose are composed after a vowel the same way.
 */
class AStableStarterThatDecomposesComposesWithNothingBeforeItTest {

    /** The code points composed after another that decompose themselves, as Unicode 18.0.0 has
     *  them. */
    private static final int[] COMPOSED_AFTER_ANOTHER = {
        0x113C5, 0x113C7, 0x113C8, 0x16121, 0x16122, 0x16123, 0x16124, 0x16125, 0x16126, 0x16127,
        0x16128, 0x16D68};

    @Test
    void aStarterBeforeItComposesWithIt() {
        String pair = Character.toString(0x16D63) + Character.toString(0x16D68);
        assertNotEquals(pair, Normalization.nfc(pair), "U+16D63 and U+16D68 compose");
    }

    @Test
    void noneOfThemIsAStableStarter() {
        CodePoints stable = StableStarters.all();
        for (int each : COMPOSED_AFTER_ANOTHER) {
            assertFalse(stable.has(each), () -> "U+" + Integer.toHexString(each)
                    + " is composed after another");
        }
    }
}
