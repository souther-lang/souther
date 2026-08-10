package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A group written down the page ends one line at each place it breaks, and not two.
 *
 * <p>The conditional-layout rule answers whether the group is written on one line or down the page,
 * which is a decision about the group and is why its witness is a pair of booleans. How many lines
 * end at one of the places it breaks is a different question, and the answer is one: a blank line
 * inside a construct is written where the author wrote a paragraph break between its members, which
 * is a forced break and is a rule that says so.
 *
 * <p>Left unanswered, a source that put a blank line at a boundary a group settles departed from a
 * canonical form no rule could name: the group did break there, so the conditional witness says
 * nothing, and no obligation stands at that boundary for the forced rules to count lines at.
 */
class AGroupsBreakEndsOneLineTest {

    private static final String BROKEN = """
            module m exposing ( f )

            data Result =
                { alpha: Int
                , beta: Int
                }

            let f (n: Int): Result =
                Result { alpha = n + 100000, beta = n + 200000, alpha = n + 300000, beta = n + 400000, alpha = n + 500000 }
            """;

    /** The construct this is about is one the width decided, and it is written down the page. */
    @Test
    void theConstructIsOneTheWidthWroteDownThePage() {
        String canonical = Formatter.format(BROKEN);

        assertTrue(canonical.contains("Result {\n"),
                "the width was expected to break it:\n" + canonical);
    }

    @Test
    void aBlankLineAtOneOfItsBreaksIsSomeRules() {
        String canonical = Formatter.format(BROKEN);
        String source = canonical.replaceFirst("alpha = n \\+ 100000,\n", "alpha = n + 100000,\n\n");

        assertTrue(!source.equals(canonical), "the source was expected to differ");
        Deviations.Report report = Deviations.of(source);

        assertTrue(!report.deviations().isEmpty(), "no rule named it");
        assertTrue(report.whole(), "and what is named is not all of it");
    }

    /** And what it says is a count of lines, which is what a blank line is one too many of. */
    @Test
    void andWhatItSaysIsHowManyLinesEndThere() {
        String canonical = Formatter.format(BROKEN);
        String source = canonical.replaceFirst("alpha = n \\+ 100000,\n", "alpha = n + 100000,\n\n");

        Deviations.Report report = Deviations.of(source);

        assertEquals(List.of("a group written down the page ends one line where it breaks"),
                report.deviations().stream().map(Deviations.Deviation::rule).toList());
        assertEquals("one line ends here", report.deviations().get(0).canonical());
        assertEquals("two do", report.deviations().get(0).source());
    }

    /** A source that wrote the construct as the canonical form does has nothing against it. */
    @Test
    void andACanonicalSourceHasNothingAgainstIt() {
        String canonical = Formatter.format(BROKEN);

        assertEquals(canonical, Formatter.format(canonical));
        assertEquals(List.of(), Deviations.of(canonical).deviations());
    }
}
