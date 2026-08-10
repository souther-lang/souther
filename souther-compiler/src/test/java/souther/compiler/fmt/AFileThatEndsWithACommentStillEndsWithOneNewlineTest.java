package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A file whose last line is a comment ends with one newline like any other, and that is the file's
 * rule rather than the comment's.
 *
 * <p>Two rules meet at the end of such a file: what stands between the last code and the comment,
 * and how the file ends. They are held against two stretches — the first against what is written
 * above the comment and the second against what follows it — because a comment rule that answered
 * for the newline after it and the file rule that answers for the same one would be one newline
 * with two rules over it.
 *
 * <p>Written because the stretch the file's rule is projected onto used to be taken from the last
 * code token, which holds a comment where one ends the file. Left alone for holding one, the rule
 * had a witness and wrote nothing; and the comment rule, asked about a comment with no line under
 * it, computed a stretch from a newline that is not there.
 */
class AFileThatEndsWithACommentStillEndsWithOneNewlineTest {

    private static final String TRAILING =
            "module fmtprobe exposing ( Alpha )\n\ndata Alpha = Int // what it is";

    private static final String ON_ITS_OWN_LINE =
            "module fmtprobe exposing ( Alpha )\n\ndata Alpha = Int\n\n// a note at the end";

    private static List<Witness> witnesses(String source, Formatter.CanonicalForm canonical) {
        List<Witness> out = new ArrayList<>(Witnesses.spacing(source, canonical));
        out.addAll(Witnesses.separation(source, canonical));
        out.addAll(Witnesses.indentation(source, canonical));
        out.addAll(Witnesses.forced(source, canonical));
        out.addAll(Witnesses.conditional(source, canonical));
        out.addAll(Witnesses.comments(source, canonical));
        return out;
    }

    /** A comment at the end of the last line, and the file ending on it. */
    @Test
    void aTrailingCommentAtTheEndOfTheFileIsAnsweredAndRepaired() {
        holds(TRAILING);
    }

    /** And a comment on a line of its own, which is the one with a line above it to answer for as
     * well. */
    @Test
    void aCommentOnItsOwnLineAtTheEndOfTheFileIsAnsweredAndRepaired() {
        holds(ON_ITS_OWN_LINE);
    }

    /** The file's rule answers for the newline after the comment, and no other rule does. */
    @Test
    void theNewlineAfterTheCommentIsTheFilesAndNoOneElsesToo() {
        for (String source : List.of(TRAILING, ON_ITS_OWN_LINE)) {
            long ends = Deviations.of(source).deviations().stream()
                    .filter(d -> d.rule().equals("a file ends with one newline"))
                    .count();
            assertEquals(1, ends, "one rule answers for how the file ends: " + source);
        }
    }

    private static void holds(String source) {
        Deviations.Report report = Deviations.of(source);

        assertTrue(!report.deviations().isEmpty(),
                "the source deviates, or this checks nothing");
        assertTrue(report.whole(),
                "everything it deviates by is named: " + report.deviations());

        Formatter.CanonicalForm canonical = Formatter.canonicalize(CstParser.parse(source).root());
        String repaired = Repair.repair(source, canonical, witnesses(source, canonical));

        assertEquals(source.lines().filter(line -> line.contains("//")).count(),
                repaired.lines().filter(line -> line.contains("//")).count(),
                "the comment is still there:\n" + repaired);
        assertEquals(Formatter.format(source), repaired);
    }
}
