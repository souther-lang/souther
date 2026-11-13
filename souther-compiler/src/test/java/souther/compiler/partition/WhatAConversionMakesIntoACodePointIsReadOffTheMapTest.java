package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.CodePoints;

import souther.compiler.evaluate.BoundUnderEvaluation;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.semantics.CodePointClass;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which code points a case conversion makes into a separator, leaves as they are, or keeps the
 * count of is read off the map the conversion is exactly ({@code CodeMap}), past the ASCII range
 * as within it, and each answer is held to what the run time converts.
 */
class WhatAConversionMakesIntoACodePointIsReadOffTheMapTest {

    private static final CaseMapping UPPER_OF_LOWER =
            new CaseMapping.Uppercase(CaseMapping.LOWERCASE);

    @Test
    void aStringIsPartedWhereTheConversionMakesACodePointIntoTheSeparator() {
        assertTrue(Partitions.partsAt('é', CaseMapping.LOWERCASE).test('É'));
        assertTrue(Partitions.partsAt('é', CaseMapping.LOWERCASE).test('é'));
        assertFalse(Partitions.partsAt('é', CaseMapping.LOWERCASE).test('e'));
        assertTrue(Partitions.partsAt('Σ', UPPER_OF_LOWER).test('σ'));
        for (int codePoint : new int[] {'É', 'é', 'σ'}) {
            String made = BoundUnderEvaluation.mapped(CaseMapping.LOWERCASE,
                    Character.toString(codePoint));
            assertTrue(!Partitions.partsAt('é', CaseMapping.LOWERCASE).test(codePoint)
                    || made.equals("é"), Character.toString(codePoint));
        }
    }

    @Test
    void aTextIsLeftAsItIsWhereEveryCodePointIsSentToItself() {
        assertTrue(Partitions.isUnchangedBy("é", CaseMapping.LOWERCASE));
        assertTrue(Partitions.isUnchangedBy("あい", UPPER_OF_LOWER));
        assertFalse(Partitions.isUnchangedBy("É", CaseMapping.LOWERCASE));
        assertFalse(Partitions.isUnchangedBy("ß", CaseMapping.UPPERCASE));
    }

    /**
     * Every count of a class is written where some code point of it is sent to itself: a run of
     * {@code あ} is its own lowercase, and a sharp s is made into two letters by uppercase, so no
     * string of it keeps the count.
     */
    @Test
    void everyCountIsWrittenWhereSomeCodePointOfTheClassIsSentToItself() {
        assertTrue(TermRealizations.writesEveryCountOf(
                new CodePointClass.OneOf(CodePoints.of('あ')), CaseMapping.LOWERCASE));
        assertTrue(BoundUnderEvaluation.mapped(CaseMapping.LOWERCASE, "あああ").equals("あああ"));
        assertFalse(TermRealizations.writesEveryCountOf(
                new CodePointClass.OneOf(CodePoints.of('ß')), CaseMapping.UPPERCASE));
        assertFalse(TermRealizations.writesEveryCountOf(
                new CodePointClass.OneOf(CodePoints.of('A')), CaseMapping.LOWERCASE));
    }
}
