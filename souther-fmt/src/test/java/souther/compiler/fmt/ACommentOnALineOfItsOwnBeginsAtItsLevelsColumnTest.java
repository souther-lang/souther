package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comment written on a line of its own begins where that line's level does.
 *
 * <p>Not a rule of its own. The layout writes the comment at the indent of the break in front of it,
 * which is the level it stands under — so the column is the indentation rule's answer and what was
 * missing is the source's side of it: a line the canonical form opens for a comment was one the
 * source could not be asked about, so a comment written anywhere at all left the report with nothing
 * to say.
 *
 * <p>The rules about comments answer the questions around it — how many lines stand between it and
 * what it is above, and what stands in front of one at the end of a line of code. Neither of them is
 * a column.
 */
class ACommentOnALineOfItsOwnBeginsAtItsLevelsColumnTest {

    @Test
    void aCommentInsideAConstructIsSomeRules() {
        String source = """
                module m

                data R =
                    { a: Int
                         // about b
                    , b: Int
                    }
                """;

        Deviations.Report report = Deviations.of(source);

        assertTrue(!report.deviations().isEmpty(), "no rule named it");
        assertTrue(report.whole(), "and what is named is not all of it");
    }

    /** One above a top-level item stands at the file's own column. */
    @Test
    void andOneAboveATopLevelItemIsToo() {
        String source = """
                module m

                    // about f
                let f (a: Int): Int = a
                """;

        Deviations.Report report = Deviations.of(source);

        assertTrue(!report.deviations().isEmpty(), "no rule named it");
        assertTrue(report.whole(), "and what is named is not all of it");
    }

    /**
     * A run of comments is written at one column, and a source that lined the second one up under
     * the first's text has moved it off that column.
     *
     * <p>This is the shape the corpus has: a comment too long for its line, continued on the next
     * and hand-aligned under the first.
     */
    @Test
    void andTheContinuationOfARunIsAtTheSameColumn() {
        String source = """
                module m

                data R =
                    { a: Int // membership, not order, and two rows for one
                                 // are not two
                    , b: Int
                    }
                """;

        Deviations.Report report = Deviations.of(source);

        assertTrue(report.whole(), "what is named is not all of it");
        assertEquals(List.of("one level deeper is one indent further in"),
                report.deviations().stream().map(Deviations.Deviation::rule).toList(),
                "the column is the indentation rule's answer, and the only one here");
    }

    /**
     * A comment the canonical form carries somewhere else has no column here.
     *
     * <p>The line the source wrote it on is one the repair is about to take away, so an indent
     * written onto it would be an expectation about a line that will not be there. This rule reads
     * the carrier decision rather than competing with it — and where it did not, the two answered
     * about the same characters and the composition refused, which is how it was found.
     */
    @Test
    void andACommentCarriedSomewhereElseIsNotThisRulesLine() {
        String source = """
                module m

                data R =
                    { a: Int
                    , b: Int
                    }

                let r: R =
                    R { a = 1
                          // about b
                        , b = 2
                        }
                """;

        Deviations.Report report = Deviations.of(source);

        assertTrue(report.whole(), "what is named is not all of it");
        assertTrue(report.deviations().stream()
                        .anyMatch(d -> d.rule().equals(
                                "a comment is carried by the construct it was written against")),
                "the comment moves, and that is what is said about it: " + report.deviations());
    }

    /** And a source that has its comments where the canonical form does has nothing against it. */
    @Test
    void andACanonicalSourceHasNothingAgainstIt() {
        String source = """
                module m

                // about R
                data R =
                    { a: Int
                    // about b
                    , b: Int
                    }
                """;

        assertEquals(source, Formatter.format(source));
        assertEquals(List.of(), Deviations.of(source).deviations());
    }
}
