package souther.compiler.fmt;

import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two rules broken on one line give both witnesses, and repairing them writes the canonical form.
 *
 * <p>This is where a repair that owned a patch each would fail. The rules answer about their own
 * units and the text those units are written in overlaps: one rewrites a line and the next is then
 * applied at an offset that line no longer has. So the expectations are composed over the units and
 * the text is written once.
 *
 * <p>The first fixture is the one this issue opened with. The padding in front of the {@code =} and
 * the record body opening down the page are two decisions on one source line, and they do not
 * disagree about anything — only about which characters they are written in.
 */
@Tag("population")
class TwoRulesOnOneLineAreBothWrittenTest {

    private static List<Witness> witnesses(String source, Formatter.CanonicalForm canonical) {
        List<Witness> out = new ArrayList<>(Witnesses.spacing(source, canonical));
        out.addAll(Witnesses.separation(source, canonical));
        out.addAll(Witnesses.indentation(source, canonical));
        out.addAll(Witnesses.forced(source, canonical));
        out.addAll(Witnesses.conditional(source, canonical));
        out.addAll(Witnesses.comments(source, canonical));
        return out;
    }

    private static String repaired(String source) {
        Formatter.CanonicalForm canonical = Formatter.canonicalize(CstParser.parse(source).root());
        return Repair.repair(source, canonical, witnesses(source, canonical));
    }

    /** A spacing decision and a layout decision on one line, and both are written. */
    @Test
    void aSpacingAndALayoutDecisionOnOneLineAreBothWritten() {
        String source = """
                module fmtprobe exposing ( EmailAddress, EmailOnly )

                data EmailAddress = String

                data EmailOnly     = { email: EmailAddress, verified: Bool, addedOn: Date }
                """;
        Formatter.CanonicalForm canonical = Formatter.canonicalize(CstParser.parse(source).root());
        List<Witness> found = witnesses(source, canonical);

        assertTrue(found.stream().anyMatch(w -> w instanceof Witness.BetweenTwoTokens),
                "the padding in front of the `=`: " + found);
        assertTrue(found.stream().anyMatch(w -> w instanceof Witness.Forced
                        || w instanceof Witness.Conditional
                        || w instanceof Witness.RunTogether),
                "and the body written down the page: " + found);
        assertEquals(Formatter.format(source), repaired(source),
                "repairing both writes the canonical form");
    }

    /**
     * An indent and the break that writes the line it is on are written in the same characters.
     * Neither is dropped and neither wins: the wider stretch already says what the narrower asks
     * for, and a repair that refused every overlap would refuse this.
     */
    @Test
    void anIndentAndTheBreakThatOpensItsLineAreBothWritten() {
        String source = """
                module fmtprobe exposing ( f )

                let f (x: Int): Int = { let a = x
                  a }
                """;

        assertEquals(Formatter.format(source), repaired(source));
    }

    /** A comment and the code around it are two rules over one line, and the comment survives. */
    @Test
    void aCommentAndTheCodeAroundItAreBothWritten() {
        String source = """
                module fmtprobe exposing ( Alpha, Beta )

                data Alpha = Int     // what it is
                data Beta = Int
                """;

        String out = repaired(source);

        assertTrue(out.contains("// what it is"), "the comment is still there:\n" + out);
        assertEquals(Formatter.format(source), out);
    }

    /** And every file of the corpus repairs to a text with as many comments as it started with. A
     * rule answering about the characters a comment is made of would take one away. */
    @Test
    void everySourceKeepsItsComments() {
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            long had = source.lines().filter(line -> line.contains("//")).count();
            long kept = repaired(source).lines().filter(line -> line.contains("//")).count();
            assertEquals(had, kept, "a repair took a comment away");
        }
    }
}
