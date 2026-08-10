package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the forced-layout rules have against a source is one witness per boundary, and each says
 * which obligation the canonical form breaks it for.
 *
 * <p>These are the rules whose unit and whose boundary are the same thing: one adjacency of two
 * members is one pair, one bracket is one bracket, one comment is one comment. That is not a general
 * fact about the rules — a group holds many boundaries and was decided once — so it is held here
 * rather than assumed everywhere.
 */
class AForcedWitnessIsOneBoundaryAndOneObligationTest {

    private static List<Witness> witnesses(String source) {
        return Witnesses.forced(source, Formatter.canonicalize(CstParser.parse(source).root()));
    }

    private static List<Obligation> obligations(String source) {
        return witnesses(source).stream()
                .map(w -> ((Witness.Forced) w).unit().obligation()).toList();
    }

    /** The canonical form of a source has nothing against it. */
    @Test
    void aSourceInItsCanonicalFormHasNoWitness() {
        assertEquals(List.of(), witnesses(Formatter.format("""
                module fmtprobe exposing ( f )

                let f (x: Int): Int =
                    {
                        let a = x
                        a
                    }
                """)));
    }

    /** Two statements of a block on one line: the pair takes two lines and the closing brace takes
     * one of its own, and each is named by its own obligation. */
    @Test
    void statementsRunTogetherNameTheMembersObligation() {
        List<Obligation> found = obligations("""
                module fmtprobe exposing ( f )

                let f (x: Int): Int = { let a = x
                    a }
                """);

        assertTrue(found.contains(Obligation.MEMBERS_TAKE_LINES_OF_THEIR_OWN),
                "the two statements share a line: " + found);
        assertTrue(found.contains(Obligation.A_BRACKET_TAKES_A_LINE_OF_ITS_OWN),
                "and the closing brace shares one with the last of them: " + found);
    }

    /**
     * A file with no final newline is one witness, it is the file's own obligation, and repairing
     * it writes the canonical form.
     *
     * <p>The file's break stands after everything and has no token on its far side, so a witness
     * for it is one nothing else in this pipeline pairs with a stretch of text. Held here because
     * a rule that is a value and a witness that is made and then reaches neither the report nor the
     * repair is the thing this issue is about.
     */
    @Test
    void aFileWithNoFinalNewlineIsAWitnessAndIsRepaired() {
        String canonical = Formatter.format("""
                module fmtprobe exposing ( Alpha )

                data Alpha = Int
                """);
        String source = canonical.stripTrailing();

        assertEquals(List.of(), obligations(canonical));
        assertEquals(List.of(Obligation.A_FILE_ENDS_WITH_ONE_NEWLINE), obligations(source));

        Formatter.CanonicalForm form = Formatter.canonicalize(CstParser.parse(source).root());
        assertEquals(canonical, Repair.repair(source, form, witnesses(source)));
    }

    /** And a file that ends with a blank line is the same witness, answered the other way. */
    @Test
    void aFileThatEndsWithABlankLineIsTheSameWitness() {
        String canonical = Formatter.format("""
                module fmtprobe exposing ( Alpha )

                data Alpha = Int
                """);
        String source = canonical + "\n";

        List<Witness> found = witnesses(source);
        assertEquals(1, found.size(), found.toString());
        Witness.Forced only = (Witness.Forced) found.get(0);
        assertEquals(1, only.canonical());
        assertEquals(2, only.source());
    }

    /**
     * The two answers, and not whether a line ends. A source with a blank line between two members
     * does end a line there — it ends two — so a witness saying it does not would be untrue of it.
     */
    @Test
    void theWitnessCountsTheLinesThatEndThere() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( f )

                let f (x: Int): Int =
                    {
                        let a = x

                        a
                    }
                """);

        Witness.Forced only = (Witness.Forced) found.stream()
                .filter(w -> ((Witness.Forced) w).unit().obligation()
                        == Obligation.MEMBERS_TAKE_LINES_OF_THEIR_OWN)
                .findFirst().orElseThrow();
        assertEquals(1, only.canonical());
        assertEquals(2, only.source(), "the source ends two lines there, and it is that that is"
                + " wrong rather than ending none");
    }

    /**
     * A comment at the end of a line is one the canonical form leaves there, so the source has
     * nothing against it.
     *
     * <p>The obligation is violable on the other side only. Nothing can follow a comment on its
     * line in a source — a line comment runs to the end of it — so the break written after one is
     * a break every source already has. The break written in front of one is not: where the
     * canonical form puts a comment on a line of its own the source may have had it inside another,
     * and over the corpus eighteen witnesses are that.
     */
    @Test
    void aCommentTheCanonicalFormLeavesAtTheEndOfALineIsNotAWitness() {
        assertTrue(!obligations("""
                module fmtprobe exposing ( f )

                let f (x: Int): Int =
                    { // what it does
                        x }
                """).contains(Obligation.NOTHING_SHARES_A_COMMENTS_LINE));
        assertTrue(!obligations("""
                module fmtprobe exposing ( f )

                // above the definition
                let f (x: Int): Int = { let a = x
                    a }
                """).contains(Obligation.NOTHING_SHARES_A_COMMENTS_LINE));
    }

    /** The separation rule is not one of these: its unit is a pair of items and its answer a count
     * of blank lines, and reporting it here as well would say one decision twice. */
    @Test
    void theSeparationRuleIsNotReportedHere() {
        assertTrue(!obligations("""
                module fmtprobe exposing ( Alpha, Beta )

                data Alpha = Int
                data Beta = Int
                """).contains(Obligation.A_BLANK_LINE_SEPARATES_TOP_LEVEL_ITEMS));
    }

    /** A break the source wrote where the canonical form writes none is not a forced rule being
     * disobeyed. The rule says a line ends there, not that no other line may. */
    @Test
    void aBreakTheSourceAddedIsNotAForcedWitness() {
        assertEquals(List.of(), witnesses("""
                module fmtprobe exposing ( f )

                let f (x: Int): Int =
                    x
                        + 1
                """));
    }
}
