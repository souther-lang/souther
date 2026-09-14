package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.NumericDomain.Bounds;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which ranges a walk is put through the proof against.
 *
 * <p>Guesses, and none of them is sound or is meant to be: what makes a range an answer is
 * {@link Induction} proving the seed lies in it and the step never leaves it. So what is fixed here
 * is which guesses are worth a check, and a list that grows costs checks and proves nothing it
 * cannot survive.
 *
 * <p>Every guess is made from the seed, which is not an accident of the list. A reduction answers
 * its seed where the container is empty, so a range the seed is outside is refused before the step
 * is read at all.
 */
class TheRangesProposedForAWalkAreMadeFromItsSeedTest {

    private static Endpoint at(long n) {
        return Endpoint.inclusive(Count.of(BigDecimal.valueOf(n)));
    }

    private static Bounds only(long n) {
        return new Bounds(at(n), at(n));
    }

    /**
     * From a seed and a step nothing is known of: the seed, and the two directions an accumulation
     * runs. The fourth — the seed joined with what the step answers — is the range with no ends here,
     * which proves nothing and is not proposed.
     */
    @Test
    void aStepNothingIsKnownOfProposesTheSeedAndTheTwoDirections() {
        assertEquals(List.of(only(0), new Bounds(at(0), null), new Bounds(null, at(0))),
                InvariantCandidates.from(only(0), new Bounds(null, null), List.of()));
    }

    /** Where the step answers something bounded without the accumulator being assumed, the seed and
     * that answer together are proposed as well — which is the whole answer for a step that does not
     * read its accumulator. */
    @Test
    void aStepThatAnswersSomethingBoundedProposesTheSeedBesideIt() {
        assertEquals(
                List.of(only(0), new Bounds(at(0), null), new Bounds(null, at(0)),
                        new Bounds(at(0), at(7))),
                InvariantCandidates.from(only(0), only(7), List.of()));
    }

    /**
     * What the step is handed is proposed beside the seed as well, which is the range a product of
     * elements at or above nought needs and no reading of the seed alone reaches.
     *
     * <p>Each input separately and no reading of which of them the step uses: a guess that follows
     * neither of a {@code Map.fold}'s two is one check and is discarded.
     */
    @Test
    void whatTheStepIsHandedIsProposedBesideTheSeed() {
        assertEquals(
                List.of(only(1), new Bounds(at(1), null), new Bounds(null, at(1)),
                        new Bounds(at(0), null)),
                InvariantCandidates.from(only(1), new Bounds(null, null),
                        List.of(new Bounds(at(0), null))));
    }

    /** A seed nothing bounds proposes nothing to prove: every range made from it is the one with no
     * ends. */
    @Test
    void aSeedNothingBoundsProposesNothing() {
        assertEquals(List.of(),
                InvariantCandidates.from(new Bounds(null, null), new Bounds(null, null), List.of()));
    }
}
