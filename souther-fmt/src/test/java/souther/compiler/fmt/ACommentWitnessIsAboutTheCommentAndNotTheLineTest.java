package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the rules about comments have against a source is one witness per comment.
 *
 * <p>Two rules, and their units are the same thing: a comment at the end of a line of code has one
 * space in front of it, and a comment on a line of its own has what it is written above on the next
 * line. A run of comments above a definition is a run of decisions, one each.
 *
 * <p>What is not here is which construct carries a comment. That is a decision the formatter takes
 * and no rule has been written for, so a source that put a comment where the canonical form writes
 * it under something else is not answered — {@link Deviations.Report#whole} is what says so.
 */
class ACommentWitnessIsAboutTheCommentAndNotTheLineTest {

    private static List<Witness> witnesses(String source) {
        return Witnesses.comments(source, Formatter.canonicalize(CstParser.parse(source).root()));
    }

    /** The canonical form of a source has nothing against it. */
    @Test
    void aSourceInItsCanonicalFormHasNoWitness() {
        assertEquals(List.of(), witnesses(Formatter.format("""
                module fmtprobe exposing ( Alpha )

                // what Alpha is
                data Alpha = Int
                """)));
    }

    /** A blank line under a comment is one witness, and it counts lines rather than naming text. */
    @Test
    void aBlankLineUnderACommentIsOneWitness() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( Alpha )

                // what Alpha is

                data Alpha = Int
                """);

        assertEquals(1, found.size(), found.toString());
        Witness.CommentAbove only = assertInstanceOf(Witness.CommentAbove.class, found.get(0));
        assertEquals(1, only.canonical(), "the thing it is about is on the next line");
        assertEquals(2, only.source());
    }

    /** A comment at the end of a line has one space in front of it, whatever the source aligned it
     * to. */
    @Test
    void aTrailingCommentAlignedByHandIsOneWitness() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( Alpha )

                data Alpha = Int      // what it is
                """);

        assertEquals(1, found.size(), found.toString());
        Witness.TrailingComment only = assertInstanceOf(Witness.TrailingComment.class, found.get(0));
        assertEquals(" ", only.canonical());
        assertEquals("      ", only.source());
    }

    /** Two comments in a run are two witnesses: each is one the formatter placed. */
    @Test
    void twoCommentsInARunAreTwoWitnesses() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( Alpha )

                // what Alpha is

                // and why

                data Alpha = Int
                """);

        assertEquals(2, found.size(), found.toString());
    }

    /** Repairing what they say writes the canonical form. */
    @Test
    void whatTheyHaveIsClosedByTheirRepair() {
        String source = """
                module fmtprobe exposing ( Alpha )

                // what Alpha is

                data Alpha = Int      // and its width
                """;
        Formatter.CanonicalForm canonical =
                Formatter.canonicalize(CstParser.parse(source).root());

        String repaired = Repair.repair(source, canonical, witnesses(source));

        assertTrue(!witnesses(source).isEmpty(), "the fixture deviates, or this checks nothing");
        assertEquals(Formatter.format(source), repaired);
    }
}
