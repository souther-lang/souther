package souther.unicode;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Why the marks {@code Normalization} holds for one run are no more than the marks of that run in
 * the text the language's operations canonicalize, so no longer than a {@code String} holds.
 *
 * <p>A run grows only by marks: a starter settles the run before it. A mark that decomposed would
 * add more than itself, but no mark that decomposes is its own NFC, so none stands in a string of
 * the language. Text that is case-mapped before it is canonicalized holds, besides such marks, only
 * starters ({@code ACaseMappingWritesOnlyCodePointsThatAreTheirOwnNfcTest}), and a starter adds at
 * most the few marks of its own decomposition.
 */
class AMarkThatDecomposesIsNeverItsOwnNfcTest {

    @Test
    void noMarkThatDecomposesIsItsOwnNfc() {
        List<String> ownNfc = new ArrayList<>();
        for (int cp = 0; cp <= Character.MAX_CODE_POINT; cp++) {
            if (Character.getType(cp) == Character.SURROGATE
                    || Normalization.combiningClass(cp) == 0
                    || Normalization.decomposeOne(cp) == null) {
                continue;
            }
            String alone = Character.toString(cp);
            if (Normalization.nfc(alone).equals(alone)) {
                ownNfc.add(Integer.toHexString(cp));
            }
        }
        assertEquals(List.of(), ownNfc);
    }
}
