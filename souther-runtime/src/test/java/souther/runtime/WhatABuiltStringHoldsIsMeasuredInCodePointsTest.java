package souther.runtime;

import org.junit.jupiter.api.Test;
import souther.unicode.Normalization;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a {@code String} holds is a number of code points (spec §what-a-string-holds), and what is
 * bounded is the string an operation builds, not the numbers it is given. The bound is the
 * language's, so these ask {@link Strings#repeat} and {@link Strings#pad} of a small one: a text
 * that long cannot be built to ask the real one, and a test that passes a count past every bound
 * says only that some bound is there.
 */
class WhatABuiltStringHoldsIsMeasuredInCodePointsTest {

    /** One code point, two UTF-16 units. */
    private static final String YOSHI = "𠮷";

    private static final long LIMIT = 5;

    @Test
    void repeatIsMeasuredInTheCopiesItBuilds() {
        assertEquals("xxxxx", Strings.repeat("x", 5, LIMIT));
        assertThrows(ConstraintViolation.class, () -> Strings.repeat("x", 6, LIMIT));
        assertThrows(ConstraintViolation.class, () -> Strings.repeat("ab", 3, LIMIT));
        assertEquals("abab", Strings.repeat("ab", 2, LIMIT));
    }

    /** Two units and one code point: five copies are five code points, not ten. */
    @Test
    void repeatCountsCodePointsAndNotUnits() {
        assertEquals(YOSHI.repeat(5), Strings.repeat(YOSHI, 5, LIMIT));
        assertThrows(ConstraintViolation.class, () -> Strings.repeat(YOSHI, 6, LIMIT));
    }

    @Test
    void repeatOfNothingIsNothingWhateverTheCount() {
        assertEquals("", Strings.repeat("", Long.MAX_VALUE, LIMIT));
        assertEquals("", Strings.repeat("x", 0, LIMIT));
        assertEquals("", Strings.repeat("x", Long.MIN_VALUE, LIMIT));
    }

    /** The count near the top of {@code Int}, which the JVM's own bound used to be, is not what
     *  decides: it is the copies' length. */
    @Test
    void aCountThatWasTheHostsBoundIsAbortedForItsCopies() {
        assertThrows(ConstraintViolation.class, () -> Strings.repeat("ab", Integer.MAX_VALUE));
        assertThrows(ConstraintViolation.class,
                () -> Strings.repeat("ab", Strings.LONGEST_TEXT / 2 + 1));
    }

    @Test
    void padWidthIsMeasuredInCodePoints() {
        assertEquals("00000", Strings.pad("", 5, "0", true, LIMIT));
        assertThrows(ConstraintViolation.class, () -> Strings.pad("", 6, "0", true, LIMIT));
        assertThrows(ConstraintViolation.class, () -> Strings.pad("x", 6, "0", false, LIMIT));
        assertEquals(YOSHI.repeat(5), Strings.pad("", 5, YOSHI, true, LIMIT));
        assertThrows(ConstraintViolation.class, () -> Strings.pad("", 6, YOSHI, true, LIMIT));
    }

    @Test
    void padBuildsNothingWhereItFillsNothingOrHasNothingToFill() {
        assertEquals("x", Strings.pad("x", Long.MAX_VALUE, "", true, LIMIT));
        assertEquals("abcdef", Strings.pad("abcdef", 3, "0", true, LIMIT));
        assertEquals("abcde", Strings.pad("abcde", 5, "0", false, LIMIT));
    }

    @Test
    void padWithNoPlaceForTheWidthAbortsWhateverTheCarrierIs() {
        assertThrows(ConstraintViolation.class,
                () -> Strings.padLeft("x", Long.MAX_VALUE, "0"));
        assertThrows(ConstraintViolation.class,
                () -> Strings.padRight("x", Strings.LONGEST_TEXT + 1, "0"));
    }

    @Test
    void theBoundIsInCodePointsWhereTextIsCanonicalized() {
        assertNotNull(Normalization.nfcWithin(YOSHI.repeat(5), 5));
        assertNull(Normalization.nfcWithin(YOSHI.repeat(6), 5));
        assertNotNull(Normalization.nfcWithin(YOSHI.repeat(4) + "é", 5));
        assertNull(Normalization.nfcWithin(YOSHI.repeat(5) + "é", 5));
    }

    @Test
    void textArrivingFromOutsideIsMeasuredInCodePoints() {
        assertEquals(new TextAdmission.Admitted(YOSHI.repeat(5)),
                Strings.admission(YOSHI.repeat(5), 5));
        assertEquals(new TextAdmission.NoPlace(), Strings.admission(YOSHI.repeat(6), 5));
    }
}
