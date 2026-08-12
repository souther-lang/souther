package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comment written before anything else in the file is on a line of its own.
 *
 * <p>Which of the two rules about comments answers was read from what stands between a comment and
 * the code in front of it: a stretch holding a line break meant the comment opens its own line. At
 * the top of a file there is no code in front of it, so that stretch is empty and the first comment
 * of every source was taken for one at the end of a line — the rule about what stands above a
 * comment was never asked, and a blank line written into the run under the header had nothing to
 * name it.
 *
 * <p>What is in front of a comment on its line is what says it, and at the top of a file that is
 * nothing.
 */
class ACommentThatOpensTheFileIsOnALineOfItsOwnTest {

    @Test
    void aBlankLineInsideTheRunThatOpensAFileIsSomeRules() {
        String source = """
                // one

                // two
                module m

                let f (a: Int): Int = a
                """;

        Deviations.Report report = Deviations.of(source);

        assertTrue(!report.deviations().isEmpty(), "no rule named it");
        assertTrue(report.whole(), "and what is named is not all of it");
        assertEquals("a comment on a line of its own is written above the line it owns",
                report.deviations().get(0).rule());
    }

    /** The same run written the way the canonical form writes it has nothing against it. */
    @Test
    void andTheRunWithNoBlankLineInItHasNothingAgainstIt() {
        String source = """
                // one
                // two
                module m

                let f (a: Int): Int = a
                """;

        assertEquals(source, Formatter.format(source));
        assertEquals(List.of(), Deviations.of(source).deviations());
    }

    /** And a comment at the end of a line of code is still that one's. */
    @Test
    void andACommentAfterCodeIsStillTheOtherRules() {
        String source = """
                module m

                let f (a: Int): Int = a     // about f
                """;

        Deviations.Report report = Deviations.of(source);

        assertEquals(List.of("a comment at the end of a line is written one space after the code"),
                report.deviations().stream().map(Deviations.Deviation::rule).toList());
    }
}
