package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The file is a level of its own, and the lines it holds begin at column zero.
 *
 * <p>The indentation rule answers about a pair of levels, and the outermost pair is the file and the
 * first level written inside it. Without the file among them the pair has one member: a line written
 * under no nesting is at a column nothing decided, and a source that indented every one of its
 * definitions departed from a canonical form no rule could name.
 *
 * <p>That is what this holds — not that the formatter writes column zero, which the golden corpus
 * has always said, but that a source writing something else is told which rule it is about.
 */
class ALineTheFileHoldsIsWrittenAtColumnZeroTest {

    @Test
    void aDefinitionWrittenFurtherInIsSomeRules() {
        String source = """
                module m

                    let f (a: Int): Int = a
                """;

        Deviations.Report report = Deviations.of(source);

        assertTrue(!report.deviations().isEmpty(), "no rule named it");
        assertTrue(report.whole(), "and what is named is not all of it");
    }

    /** The header opens the file and is written at that level too. */
    @Test
    void andSoIsTheHeaderTheFileOpensWith() {
        String source = """
                  module m

                let f (a: Int): Int = a
                """;

        Deviations.Report report = Deviations.of(source);

        assertTrue(!report.deviations().isEmpty(), "no rule named it");
        assertTrue(report.whole(), "and what is named is not all of it");
    }

    /**
     * And the deviation is the indentation rule's, at the file's level.
     *
     * <p>Written out because a source indented at the top level also has every line under it
     * indented, and a report naming the levels inside would tell an author to move lines whose step
     * is right.
     */
    @Test
    void andTheRuleItNamesIsTheOneAboutColumns() {
        String source = """
                module m

                    let f (a: Int): Int = a
                """;

        Deviations.Report report = Deviations.of(source);

        assertEquals(1, report.deviations().size(), "one decision, and: " + report.deviations());
        assertEquals("a line the file holds begins at column zero",
                report.deviations().get(0).rule());
    }

    /** A source already in canonical form has nothing against it, so the rule is not answering
     *  about every line there is. */
    @Test
    void andACanonicalSourceHasNothingAgainstIt() {
        String source = """
                module m

                let f (a: Int): Int = a
                """;

        assertEquals(source, Formatter.format(source));
        assertEquals(List.of(), Deviations.of(source).deviations());
    }
}
