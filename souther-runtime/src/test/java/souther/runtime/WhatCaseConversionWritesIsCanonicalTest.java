package souther.runtime;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What {@link Strings#lowercase} and {@link Strings#uppercase} answer is NFC, as every String is.
 *
 * <p>Case conversion and normalization are each 199x-notation's, and each is tested there. That a
 * String carries NFC is this language's, and so is the decision to normalize what the case
 * conversion wrote: neither half tested on its own says the two are composed. So each is asked of
 * an input that is NFC and whose mapping alone is not — the mapping leaves a letter and a combining
 * mark that compose — and the answer has to be the composed character. Answered with the mapping
 * alone, it would be the pair.
 */
class WhatCaseConversionWritesIsCanonicalTest {

    @Test
    void lowercaseComposesWhatItsMappingLeftApart() {
        // H and COMBINING MACRON BELOW: h and the mark compose to LATIN SMALL LETTER H WITH LINE
        // BELOW, and H and the mark do not compose at all.
        assertEquals("ẖ", Strings.lowercase("H̱"));
    }

    @Test
    void uppercaseComposesWhatItsMappingLeftApart() {
        // i and COMBINING DOT ABOVE: I and the mark compose to LATIN CAPITAL LETTER I WITH DOT ABOVE,
        // and i and the mark do not.
        assertEquals("İ", Strings.uppercase("i̇"));
    }
}
