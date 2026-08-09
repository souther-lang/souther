package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * What the separation rule has against a source is one witness per pair of items, and the answer is
 * a count of blank lines.
 *
 * <p>A blank line is two breaks at one adjacency. The rule was asked once — what stands between
 * these two items — so a witness per break would be reporting the newlines the layout wrote rather
 * than the decision it took.
 *
 * <p>The canonical side is read from the decision and the source side from the text. That is not an
 * inconsistency: a canonical form has decisions to be asked and a source has only what someone
 * typed.
 */
class ASeparationWitnessIsAboutTheTwoItemsNotTheBreaksTest {

    private static List<Witness> witnesses(String source) {
        return Witnesses.separation(source, Formatter.canonicalize(CstParser.parse(source).root()));
    }

    /** The canonical form of a source has nothing against it. */
    @Test
    void aSourceInItsCanonicalFormHasNoWitness() {
        assertEquals(List.of(), witnesses(Formatter.format("""
                module fmtprobe exposing ( Alpha, Beta )

                import some.place ( gamma )

                data Alpha = Int

                data Beta = Int
                """)));
    }

    /** Two items run together are one witness, and it says one blank line against none. */
    @Test
    void twoItemsWithNoBlankLineAreOneWitness() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( Alpha, Beta )

                data Alpha = Int
                data Beta = Int
                """);

        assertEquals(1, found.size(), "one pair of items was written wrongly: " + found);
        Witness.Separation only = assertInstanceOf(Witness.Separation.class, found.get(0));
        assertEquals(1, only.canonical());
        assertEquals(0, only.source());
    }

    /** And two blank lines are the same one decision, answered with two. */
    @Test
    void twoBlankLinesAreOneWitnessToo() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( Alpha, Beta )

                data Alpha = Int


                data Beta = Int
                """);

        assertEquals(1, found.size(), found.toString());
        assertEquals(2, ((Witness.Separation) found.get(0)).source());
    }

    /** An import after the header takes no blank line, so a source that writes one deviates. */
    @Test
    void aBlankLineBeforeAnImportIsAWitness() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( Alpha )

                import some.place ( gamma )
                data Alpha = Int
                """);

        assertEquals(2, found.size(), "the header before the import, and the import before the"
                + " data definition: " + found);
        assertEquals(List.of(0, 1),
                found.stream().map(w -> ((Witness.Separation) w).canonical()).toList(),
                "the first pair takes none and the second takes one");
        assertEquals(List.of(1, 0),
                found.stream().map(w -> ((Witness.Separation) w).source()).toList());
    }

    /** Two pairs written wrongly are two witnesses, each naming its own. */
    @Test
    void twoPairsWrongAreTwoWitnesses() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( Alpha, Beta, Gamma )

                data Alpha = Int
                data Beta = Int
                data Gamma = Int
                """);

        assertEquals(2, found.size(), found.toString());
        assertNotEquals(((Witness.Separation) found.get(0)).unit(),
                ((Witness.Separation) found.get(1)).unit(),
                "each witness names its own pair of items");
    }

    /** A comment between two items belongs to the second, and what stands in front of it is the
     * separation. A source that wrote the blank line before the comment has written it. */
    @Test
    void aCommentBetweenTwoItemsDoesNotCountAsWhatSeparatesThem() {
        assertEquals(List.of(), witnesses("""
                module fmtprobe exposing ( Alpha, Beta )

                data Alpha = Int

                // what Beta is for
                data Beta = Int
                """));
    }
}
