package souther.runtime;

import souther.unicode.Normalization;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every mark a case conversion writes in place of another is its own NFC, as every code point of a
 * string of the language is; what it writes that is not its own NFC is a starter. So the marks of
 * the case-mapped text {@code lowercase} and {@code uppercase} canonicalize do not decompose, which
 * is what bounds the marks {@code Normalization} holds for one run of it
 * ({@code AMarkThatDecomposesIsNeverItsOwnNfcTest}).
 */
class ACaseMappingWritesOnlyCodePointsThatAreTheirOwnNfcTest {

    @Test
    void everyMarkAMappingWritesIsItsOwnNfc() {
        Set<String> marksNotTheirOwn = new TreeSet<>();
        for (CaseTables.Mapping table : List.of(CaseTables.LOWER, CaseTables.UPPER, CaseTables.FINAL_SIGMA)) {
            for (int[] written : table.mapped()) {
                for (int cp : written) {
                    String alone = Character.toString(cp);
                    if (Normalization.combiningClass(cp) != 0 && !Normalization.nfc(alone).equals(alone)) {
                        marksNotTheirOwn.add(Integer.toHexString(cp));
                    }
                }
            }
        }
        assertEquals(Set.of(), marksNotTheirOwn);
    }
}
