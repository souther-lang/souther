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
 *
 * <p>That a family is composed at all is held by the compiler. {@link Repair} switches over
 * {@link Witness} without a default, so a rule whose expectation is added and not composed does not
 * build.
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

    /**
     * A level that moves takes what is nested inside it along. Those deeper levels have nothing
     * against them — their step is right and it is the column underneath that changed — so a repair
     * that moved only the lines written at the level named would leave them behind.
     *
     * <p>The source here is the canonical form with both levels shifted out by two, which is one
     * witness: the outer step is wrong and the inner step is not.
     */
    @Test
    void aLevelThatMovesTakesWhatIsNestedInsideItAlong() {
        String canonical = Formatter.format("""
                module fmtprobe exposing ( V, f )

                data V = Alpha | Beta

                let f (v: V, x: Int): Int =
                    {
                        let a =
                            match v with
                            | Alpha -> x
                            | Beta -> 0
                        a
                    }
                """);
        String source = reindent(reindent(canonical, 4, 6), 8, 10);
        Formatter.CanonicalForm form = Formatter.canonicalize(CstParser.parse(source).root());
        List<Witness> found = Witnesses.indentation(source, form);

        assertEquals(1, found.size(), "one step was got wrong: " + found);
        assertEquals(canonical, Repair.repair(source, form, found),
                "and repairing that one step writes the canonical form, deeper lines and all");
    }

    /** The same text with every line indented by {@code from} written at {@code to} instead. */
    private static String reindent(String text, int from, int to) {
        List<String> out = new ArrayList<>();
        for (String line : text.split("\n", -1)) {
            int indent = line.length() - line.stripLeading().length();
            out.add(!line.isBlank() && indent == from ? " ".repeat(to) + line.substring(from)
                    : line);
        }
        return String.join("\n", out);
    }

    /**
     * A family that cannot answer says so with a kind of its own, and a broken invariant does not.
     *
     * <p>{@link Deviations} leaves a family out of its report where it cannot answer. Told by the
     * same exception a broken invariant throws, it would leave that out too and say the report is
     * merely not whole — a defect reported as this source being unusual.
     */
    @Test
    void afamilyThatCannotAnswerSaysSoWithAKindOfItsOwn() {
        String lifted = """
                module fmtprobe exposing ( f )

                let f = (x) -> x
                """;
        Formatter.CanonicalForm canonical =
                Formatter.canonicalize(CstParser.parse(lifted).root());

        assertThrows(Witnesses.NoCorrespondence.class,
                () -> Witnesses.spacing(lifted, canonical),
                "the canonical form writes tokens this source has not");
        assertTrue(!IllegalStateException.class.isAssignableFrom(Witnesses.NoCorrespondence.class),
                "and it is not the kind a broken invariant throws, which is what lets a caller"
                        + " leave one out of a report and let the other be seen");
    }
}
