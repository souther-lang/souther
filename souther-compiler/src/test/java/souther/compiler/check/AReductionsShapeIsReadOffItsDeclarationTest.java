package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The two halves of what the checks know about a walk from a seed (ADR-0097): that an operation is
 * one is written down, and where its seed and accumulator are is read off its declaration.
 *
 * <p>The second half is what this is mostly about. {@code List.foldRight} takes its element first and
 * its accumulator second, the other way round from {@code List.foldFrom}, and nothing is written
 * about either — so a table that had written the positions out would have had a row per operation to
 * keep right, and this is the check that it does not.
 */
class AReductionsShapeIsReadOffItsDeclarationTest {

    private static ValueName op(String alias, String name) {
        return new ValueName.Stdlib(alias, name);
    }

    /** The walk itself: the seed is the second argument, and it arrives on the step's first
     * parameter. */
    @Test
    void aFoldFromCarriesItsAccumulatorOnTheFirstParameter() {
        assertEquals(new Reductions.Reduction(1, 0), Reductions.of(op("List", "foldFrom")));
    }

    /** The same walk over the container reversed, whose step takes the element first. Read off the
     * declaration, so the difference costs nothing to know. */
    @Test
    void aFoldRightCarriesItsAccumulatorOnTheSecondParameter() {
        assertEquals(new Reductions.Reduction(1, 1), Reductions.of(op("List", "foldRight")));
    }

    /** A walk over a container with no order is read the same way: what the rule licenses says
     * nothing about the order elements arrive in. */
    @Test
    void aWalkOverAContainerWithNoOrderIsReadAlike() {
        assertEquals(new Reductions.Reduction(1, 0), Reductions.of(op("Set", "fold")));
        assertEquals(new Reductions.Reduction(1, 0), Reductions.of(op("Map", "fold")));
    }

    /** A sugar has no declaration of its own, so what is true of the call it becomes is true of it
     * over the arguments that stand where they stood. */
    @Test
    void theSugarIsAnsweredByWhatItBecomes() {
        assertEquals(Reductions.of(op("List", "foldFrom")), Reductions.of(op("List", "fold")));
    }

    /** An operation that hands its closure the container's elements and is not a walk from a seed
     * answers nothing here. */
    @Test
    void anOperationThatIsNotAWalkAnswersNothing() {
        assertNull(Reductions.of(op("List", "map")));
        assertNull(Reductions.of(op("List", "filter")));
        assertNull(Reductions.of(op("List", "all")));
        assertNotNull(Combinators.of(op("List", "map")),
                "which is not the same as its handing its closure nothing");
    }

    /** Every operation with a rule is one the question is asked of, which is what keeps a rule from
     * sitting under a name nothing reaches. Held both ways round in
     * {@code AnOperationTheLibraryGainsIsAnsweredForTest}; here for this question alone. */
    @Test
    void everyWalkWrittenDownIsOneTheQuestionIsAskedOf() {
        for (ValueName operation : Reductions.answered()) {
            assertTrue(Question.REDUCTION.asksOfOperation(DefaultStdlib.get(), operation.toString()),
                    operation + " has a rule and is not asked whether it is a walk");
        }
    }

    // --- what ranges are proposed ---------------------------------------------------------------

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
