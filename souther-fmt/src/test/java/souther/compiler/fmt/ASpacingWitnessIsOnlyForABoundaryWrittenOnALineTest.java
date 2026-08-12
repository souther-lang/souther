package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxKind;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the spacing rule has against a source is one witness per boundary the canonical form writes
 * on a line, and none for the boundaries it breaks.
 *
 * <p>This is the one family where a difference in the text and a decision are the same count: one
 * adjacency is one evaluation of the rule. What it is not is every difference at an adjacency. A
 * source that wrote a space where the canonical form writes a line break has not spaced anything
 * wrongly, and the report this replaces said of twenty-one such boundaries that a space should be a
 * different space.
 */
class ASpacingWitnessIsOnlyForABoundaryWrittenOnALineTest {

    private static List<Witness> witnesses(String source) {
        return Witnesses.spacing(source, Formatter.canonicalize(CstParser.parse(source).root()));
    }

    /** The canonical form of a source has nothing against it. */
    @Test
    void aSourceInItsCanonicalFormHasNoWitness() {
        assertEquals(List.of(), witnesses(Formatter.format("""
                module fmtprobe exposing ( f )

                let f (x: Int): Int = x + 1
                """)));
    }

    /** A space the canonical form does not write is one witness, and it says both answers. */
    @Test
    void aSpaceTheCanonicalFormDoesNotWriteIsAWitness() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( f )

                let f (x: Int): Int = g( x )
                """);

        assertEquals(2, found.size(), "the two boundaries inside the call: " + found);
        Witness.BetweenTwoTokens first =
                assertInstanceOf(Witness.BetweenTwoTokens.class, found.get(0));
        assertEquals("", first.canonical());
        assertEquals(" ", first.source());
        assertEquals(SyntaxKind.ARG_LIST, first.unit().joining(),
                "the construct the rule was asked about, and it is the argument list rather than"
                        + " whatever the boundaries at the ends of the file would have shifted it to");
        assertEquals(SyntaxKind.LPAREN, first.unit().left());
        assertEquals(SyntaxKind.IDENT, first.unit().right());
    }

    /**
     * A boundary the canonical form always breaks is not this rule's, whatever the source wrote
     * there. The source has an invariant on the declaration's line and the canonical form writes it
     * on its own; what is wrong is not the space.
     */
    @Test
    void aBoundaryTheCanonicalFormBreaksIsNotASpacingWitness() {
        String source = """
                module fmtprobe exposing ( P )

                data P = Int invariant value > 0
                """;

        assertTrue(Formatter.format(source).contains("\n    invariant"),
                "the canonical form writes the invariant on a line of its own, which is what makes"
                        + " this fixture the one it is:\n" + Formatter.format(source));
        assertEquals(List.of(), witnesses(source),
                "the space in front of `invariant` is not a spacing decision, because the canonical"
                        + " form writes no spacing there");
    }

    /**
     * A boundary no group settles is this rule's whatever the source wrote there, a line break
     * included. The canonical form writes the two tokens on one line and there is no decision above
     * this one that could have put them on two.
     */
    @Test
    void aTightBoundaryTheSourceBrokeIsASpacingWitness() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( Alpha
                , Beta )

                data Alpha = Int

                data Beta = Int
                """);

        assertEquals(1, found.size(), found.toString());
        Witness.BetweenTwoTokens only = (Witness.BetweenTwoTokens) found.get(0);
        assertEquals("", only.canonical());
        assertTrue(only.source().indexOf('\n') >= 0, "what the source wrote there is a line break");
    }

    /** But a boundary a group settles is that group's: reporting the break here as well would say
     * one thing twice. */
    @Test
    void aBoundaryTheSourceBrokeIsNotASpacingWitness() {
        assertEquals(List.of(), witnesses("""
                module fmtprobe exposing ( f )

                let f (x: Int): Int = x
                    + 1
                """));
    }

    /** Two boundaries spaced wrongly are two witnesses: one adjacency is one evaluation. */
    @Test
    void twoBoundariesAreTwoWitnesses() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( f )

                let f (x: Int): Int = x+1
                """);

        assertEquals(2, found.size(), "the two sides of the operator: " + found);
        assertEquals(List.of(0, 1),
                found.stream().map(w -> ((Witness.BetweenTwoTokens) w).unit().adjacency())
                        .map(i -> i - ((Witness.BetweenTwoTokens) found.get(0)).unit().adjacency())
                        .toList(),
                "and they are two adjacencies of the token stream, next to each other");
    }
}
