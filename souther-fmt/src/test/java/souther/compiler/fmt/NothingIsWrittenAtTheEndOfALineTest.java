package souther.compiler.fmt;

import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line ends where what is written on it does.
 *
 * <p>The layout writes whitespace after a newline, as the indent of the line it opens, and never
 * before one. So a source with a space at the end of a line has departed from the canonical form —
 * and the rules that answer about the same characters do not say it: the break rules count how many
 * lines end at a boundary, the spacing rule answers about boundaries written on a line, and a
 * blank line carrying spaces is at no level's column.
 *
 * <p>Every line of the source, and not only the ones the canonical form has. What the rule expects
 * is nothing, which is true of a line wherever it stands, so this needs no correspondence to ask.
 */
@Tag("population")
class NothingIsWrittenAtTheEndOfALineTest {

    @Test
    void aSpaceAfterTheLastTokenOfALineIsSomeRules() {
        String source = "module m\n\nlet f (a: Int): Int = a   \n";

        Deviations.Report report = Deviations.of(source);

        assertTrue(!report.deviations().isEmpty(), "no rule named it");
        assertTrue(report.whole(), "and what is named is not all of it");
        assertEquals("a line ends where what is written on it does",
                report.deviations().get(0).rule());
    }

    /** A blank line carrying spaces is a line with nothing on it and something at the end of it. */
    @Test
    void andSoAreTheSpacesOnABlankLine() {
        String source = "module m\n    \nlet f (a: Int): Int = a\n";

        Deviations.Report report = Deviations.of(source);

        assertTrue(!report.deviations().isEmpty(), "no rule named it");
        assertTrue(report.whole(), "and what is named is not all of it");
    }

    /**
     * The expectation is the canonical form's own: over the corpus it writes no line that ends in
     * whitespace.
     *
     * <p>Written as a measurement of the output rather than of the document, because what a reader
     * has in hand is the text.
     */
    @Test
    void andTheCanonicalFormWritesNoneOfIt() {
        List<String> found = new ArrayList<>();
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            for (String line : Formatter.format(source).split("\n", -1)) {
                if (!line.equals(line.stripTrailing())) {
                    found.add(line);
                }
            }
        }

        assertEquals(List.of(), found, "the canonical form ends a line with whitespace");
    }

    /** And a source with none of it has nothing against it. */
    @Test
    void andASourceWithNoneOfItHasNothingAgainstIt() {
        String source = "module m\n\nlet f (a: Int): Int = a\n";

        assertEquals(source, Formatter.format(source));
        assertEquals(List.of(), Deviations.of(source).deviations());
    }
}
