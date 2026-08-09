package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * What the indentation rule has against a source is one witness per pair of levels it got wrong,
 * and not one per line.
 *
 * <p>A source that indents a construct by two writes every line inside it in the wrong column. The
 * rule was evaluated once — the inner level is one indent further in than the outer, and it is not —
 * so a report per line would be counting the text and calling the count decisions.
 *
 * <p>Every fixture here is the canonical form with its indentation moved and nothing else changed,
 * built by {@link #reindent}. A source hand-written to look wrong deviates in more ways than the one
 * being held, and then a test claiming one witness is claiming something about the others too.
 */
class AnIndentationWitnessNamesTheLevelsAndNotTheLinesTest {

    private static final String ONE_LEVEL = Formatter.format("""
            module fmtprobe exposing ( f )

            let f (x: Int): Int =
                {
                    let a = x
                    a
                }
            """);

    private static final String TWO_LEVELS = Formatter.format("""
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

    private static List<Witness> witnesses(String source) {
        return Witnesses.indentation(source,
                Formatter.canonicalize(CstParser.parse(source).root()));
    }

    /** The canonical form of a source has nothing against it. */
    @Test
    void aSourceInItsCanonicalFormHasNoWitness() {
        assertEquals(List.of(), witnesses(ONE_LEVEL));
        assertEquals(List.of(), witnesses(TWO_LEVELS));
    }

    /** A level written two columns short is one witness, and it names the step and not a column. */
    @Test
    void aLevelWrittenTooFarOutIsOneWitness() {
        List<Witness> found = witnesses(reindent(ONE_LEVEL, 4, 6));

        assertEquals(1, found.size(), "one step was got wrong: " + found);
        Witness.Indentation only = assertInstanceOf(Witness.Indentation.class, found.get(0));
        assertEquals(4, only.canonical());
        assertEquals(6, only.source());
    }

    /** And the count does not follow the number of lines the level holds. */
    @Test
    void andTheSameStepWrongOverMoreLinesIsStillOneWitness() {
        String longer = Formatter.format("""
                module fmtprobe exposing ( f )

                let f (x: Int): Int =
                    {
                        let a = x
                        let b = a
                        let c = b
                        let d = c
                        d
                    }
                """);

        assertEquals(witnesses(reindent(ONE_LEVEL, 4, 6)).size(),
                witnesses(reindent(longer, 4, 6)).size(),
                "four more lines at the same wrong column are the same one decision");
        assertEquals(1, witnesses(reindent(longer, 4, 6)).size());
    }

    /**
     * A level moved with the one above it kept its step, and the rule has nothing against it. This
     * is what makes the unit a pair: the columns are all wrong and one step is.
     */
    @Test
    void aLevelMovedWithTheOneAboveItKeepsItsStep() {
        List<Witness> found = witnesses(reindent(reindent(TWO_LEVELS, 4, 6), 8, 10));

        assertEquals(1, found.size(),
                "the inner level is still four further in than the outer: " + found);
        assertEquals(6, ((Witness.Indentation) found.get(0)).source());
    }

    /** Two steps got wrong are two witnesses, each naming a pair of levels of its own. */
    @Test
    void twoStepsWrongAreTwoWitnesses() {
        List<Witness> found = witnesses(reindent(reindent(TWO_LEVELS, 4, 6), 8, 14));

        assertEquals(2, found.size(), "two steps were got wrong: " + found);
        assertNotEquals(((Witness.Indentation) found.get(0)).unit(),
                ((Witness.Indentation) found.get(1)).unit(),
                "each witness names a pair of levels of its own");
        assertEquals(List.of(6, 8),
                found.stream().map(w -> ((Witness.Indentation) w).source()).sorted().toList());
    }

    /** A source that broke somewhere the canonical form does not is not this rule's to report: the
     * line it wrote has no level to be at, and the break rules answer for it. */
    @Test
    void aSourceThatDidNotBreakWhereTheCanonicalFormDoesIsNotAnIndentationWitness() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( f )

                let f (x: Int): Int = { let a = x
                    a }
                """);

        assertEquals(List.of(), found,
                "what this source got wrong is where it breaks, not how far in: " + found);
    }

    /** The same text with every line indented by {@code from} written at {@code to} instead. Only
     *  the indentation moves: what is on the line is written on verbatim. */
    private static String reindent(String text, int from, int to) {
        List<String> out = new ArrayList<>();
        for (String line : text.split("\n", -1)) {
            int indent = line.length() - line.stripLeading().length();
            out.add(!line.isBlank() && indent == from ? " ".repeat(to) + line.substring(from)
                    : line);
        }
        return String.join("\n", out);
    }
}
