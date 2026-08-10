package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the conditional-layout rule has against a source is one witness per group, and not one per
 * boundary the group moved.
 *
 * <p>A record literal written down the page moves every member boundary it holds. The rule was
 * asked once — does the line this would take fit the width — so the unit is the group.
 *
 * <p>And the match is against the opportunities. Where the canonical form keeps a group whole there
 * is no break of its own to point at, and a source that broke inside it has still departed from the
 * decision; a report built from the breaks the layout wrote would have nothing to say about the
 * commonest deviation there is.
 *
 * <p>One witness per group is how many there are, and it stands at the first place the source
 * settled the other way rather than at the head of the construct. Which of the two it is depends on
 * what differs: a source that wrote whole what the canonical form writes down the page disagrees
 * about the form, and one that wrote it down the page and ran some of its places together agrees
 * about the form and differs at those places.
 */
class AConditionalWitnessIsAboutTheGroupAndNotItsBoundariesTest {

    private static List<Witness> witnesses(String source) {
        return Witnesses.conditional(source,
                Formatter.canonicalize(CstParser.parse(source).root()));
    }

    /** The canonical form of a source has nothing against it. */
    @Test
    void aSourceInItsCanonicalFormHasNoWitness() {
        assertEquals(List.of(), witnesses(Formatter.format("""
                module fmtprobe exposing ( P, f )

                data P = { alpha: Int, beta: Int }

                let f (x: Int): P = P { alpha = x, beta = x }
                """)));
    }

    /**
     * A source that broke a group the canonical form keeps whole is one witness — and this is the
     * case the layout wrote no break for, so nothing it realized could have carried it.
     */
    @Test
    void aGroupTheSourceBrokeAndTheCanonicalFormKeepsWholeIsAWitness() {
        List<Witness> found = witnesses("""
                module fmtprobe exposing ( P, f )

                data P = { alpha: Int, beta: Int }

                let f (x: Int): P =
                    P { alpha = x
                      , beta = x
                      }
                """);

        assertTrue(!found.isEmpty(), "the source wrote down the page what fits on a line");
        Witness.Conditional first = assertInstanceOf(Witness.Conditional.class, found.get(0));
        assertTrue(first.canonicalIsWhole(), "the canonical form writes it on one line");
        assertTrue(!first.sourceIsWhole(), "and the source did not");
    }

    /** And the count follows the groups, not the boundaries under them. A literal with four
     * members moves four boundaries and is the same one decision as a literal with two. */
    @Test
    void andMoreMembersUnderOneGroupAreTheSameCount() {
        List<Witness> two = witnesses("""
                module fmtprobe exposing ( P, f )

                data P = { alpha: Int, beta: Int }

                let f (x: Int): P =
                    P { alpha = x
                      , beta = x
                      }
                """);
        List<Witness> four = witnesses("""
                module fmtprobe exposing ( P, f )

                data P = { alpha: Int, beta: Int, gamma: Int, delta: Int }

                let f (x: Int): P =
                    P { alpha = x
                      , beta = x
                      , gamma = x
                      , delta = x
                      }
                """);

        assertTrue(!two.isEmpty(), "the fixture deviates, or this compares nothing: " + two);
        assertEquals(two.size(), four.size(),
                "two more member boundaries under the same group are the same one decision: "
                        + two + " against " + four);
    }

    /**
     * A group written down the page because it holds a forced break is never said to be one the
     * canonical form keeps whole. Telling an author to close the line up would be telling them to
     * undo what the forced rule wrote, and the width decided nothing here to tell them about.
     */
    @Test
    void aGroupBrokenByWhatItHoldsIsNeverSaidToBeKeptWhole() {
        String source = """
                module fmtprobe exposing ( f )

                let f (x: Int): Int = { let a = x
                    a }
                """;

        for (Witness w : witnesses(source)) {
            if (w instanceof Witness.Conditional c) {
                assertTrue(!c.canonicalIsWhole(),
                        "no witness may say the canonical form keeps whole a construct it writes"
                                + " down the page for a reason of its own: " + c);
                assertInstanceOf(Outcome.BrokenByForcedLayout.class, c.why(),
                        "and it carries what put it down the page: " + c);
            }
        }
    }
}
