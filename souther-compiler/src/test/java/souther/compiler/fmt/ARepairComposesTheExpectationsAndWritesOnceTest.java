package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A repair composes what the witnesses expect and writes the source once.
 *
 * <p>A witness owns no patch. Two of them land on one line of the canonical form often enough that
 * this is not hypothetical, and a repair applied one at a time would rewrite a line and then apply
 * the next at an offset that line no longer has.
 *
 * <p>What is held here is that a family's witnesses close under its own repair: repair the source
 * and ask again, and there is nothing left. That is what makes the distance to the canonical form a
 * number that has to fall as each family lands, rather than a check that cannot be run until the
 * last one is in.
 */
class ARepairComposesTheExpectationsAndWritesOnceTest {

    private static String repairSpacingAndSeparation(String source) {
        Formatter.CanonicalForm canonical = Formatter.canonicalize(CstParser.parse(source).root());
        List<Witness> witnesses = new ArrayList<>();
        witnesses.addAll(Witnesses.spacing(source, canonical));
        witnesses.addAll(Witnesses.separation(source, canonical));
        return Repair.repair(source, canonical, witnesses);
    }

    private static List<Witness> witnesses(String source) {
        Formatter.CanonicalForm canonical = Formatter.canonicalize(CstParser.parse(source).root());
        List<Witness> out = new ArrayList<>(Witnesses.spacing(source, canonical));
        out.addAll(Witnesses.separation(source, canonical));
        return out;
    }

    /** The spacing witnesses of a source are gone from its repair. */
    @Test
    void whatTheSpacingRuleHadIsClosedByItsRepair() {
        String source = """
                module fmtprobe exposing ( f )

                let f (x: Int): Int = g( x )+1
                """;

        assertTrue(!witnesses(source).isEmpty(), "the fixture deviates, or this checks nothing");
        assertEquals(List.of(), witnesses(repairSpacingAndSeparation(source)));
    }

    /**
     * And two families' expectations over one source compose. This is the shape that is not
     * hypothetical: the spacing on a line and the blank lines above it are two decisions, and a
     * repair that wrote one and then looked for the other would look in the wrong place.
     */
    @Test
    void twoFamiliesOverOneSourceCompose() {
        String source = """
                module fmtprobe exposing ( Alpha, f )

                data Alpha = Int
                let f (x: Int): Int = g( x )
                """;

        List<Witness> had = witnesses(source);
        assertTrue(had.stream().anyMatch(w -> w instanceof Witness.BetweenTwoTokens), had.toString());
        assertTrue(had.stream().anyMatch(w -> w instanceof Witness.Separation), had.toString());

        String repaired = repairSpacingAndSeparation(source);
        assertEquals(List.of(), witnesses(repaired));
        assertEquals("""
                module fmtprobe exposing ( Alpha, f )

                data Alpha = Int

                let f (x: Int): Int = g(x)
                """, repaired);
    }

    /** A family whose expectation is not composed yet is refused rather than left out. A repair
     * that skipped one would answer with a text that is not the canonical form and say nothing. */
    @Test
    void aFamilyWithNoExpectationYetIsRefused() {
        String source = """
                module fmtprobe exposing ( f )

                let f (x: Int): Int =
                    {
                      let a = x
                      a
                    }
                """;
        Formatter.CanonicalForm canonical = Formatter.canonicalize(CstParser.parse(source).root());
        List<Witness> indentation = Witnesses.indentation(source, canonical);

        assertTrue(!indentation.isEmpty(), "the fixture deviates, or this checks nothing");
        assertThrows(IllegalArgumentException.class,
                () -> Repair.repair(source, canonical, indentation));
    }
}
