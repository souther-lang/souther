package souther.compiler.regex;

import net.unit8.notation199x.Normalization;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A stable starter composes with nothing before it, even where it decomposes itself. Kirat Rai's
 * U+16D68 decomposes, so it stands in no composite's full decomposition, and still U+16D63 before it
 * composes with it into U+16D6A: a string of the two is not NFC, and it is no stable starter.
 */
class AStableStarterThatDecomposesComposesWithNothingBeforeItTest {

    @Test
    void aCodePointACompositionTakesAsItsLaterHalfIsNoStableStarter() {
        String pair = Character.toString(0x16D63) + Character.toString(0x16D68);
        assertNotEquals(pair, Normalization.nfc(pair), "the two compose");
        assertFalse(StableStarters.all().has(0x16D68), "so the later is no stable starter");
    }
}
