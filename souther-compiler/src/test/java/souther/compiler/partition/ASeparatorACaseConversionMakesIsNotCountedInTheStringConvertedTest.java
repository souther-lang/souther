package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.semantics.CaseMapping;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The separators a string holds are as many as the pieces of the string converted are parted at
 * only where the conversion makes no separator of its own. A comma it makes of nothing else. But
 * {@code ŉ} is answered {@code ʼN} in uppercase, so a string holding no {@code ʼ} converts to one
 * with a piece after a {@code ʼ}; and a capital sigma closing a word is lowercased to {@code ς}, which
 * it is not alone. Neither separator's count in the string says how its converted pieces are
 * parted.
 */
class ASeparatorACaseConversionMakesIsNotCountedInTheStringConvertedTest {

    @Test
    void aCommaIsCountedTheWayTheUppercasedPiecesArePartedAt() {
        assertTrue(UndividedByARelation.countsTheSeparatorsTheWayThePiecesAreParted(
                CaseMapping.NONE, CaseMapping.UPPERCASE, ','));
    }

    @Test
    void anApostropheUppercasingMakesIsNot() {
        assertFalse(UndividedByARelation.countsTheSeparatorsTheWayThePiecesAreParted(
                CaseMapping.NONE, CaseMapping.UPPERCASE, 0x02BC));
    }

    @Test
    void aFinalSigmaLowercasingMakesBesideALetterIsNot() {
        assertFalse(UndividedByARelation.countsTheSeparatorsTheWayThePiecesAreParted(
                CaseMapping.NONE, CaseMapping.LOWERCASE, 0x03C2));
    }

    /** A Hangul syllable has no case and nothing is sent to it, and it is what two jamo compose
     *  into: a normalization of what was converted is not shown to make none. */
    @Test
    void aCompositeANormalizationMayMakeIsNot() {
        assertFalse(UndividedByARelation.countsTheSeparatorsTheWayThePiecesAreParted(
                CaseMapping.NONE, CaseMapping.LOWERCASE, 0xAC00));
    }
}
