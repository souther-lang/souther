package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A search handed a region the rules were already shown to leave nothing in comes back with the
 * proof, having walked nothing.
 *
 * <p><b>Both halves, and the second is the one an author feels.</b> Every value such a region offers
 * is one the rules refuse, so a walk of it reaches nothing however long it goes — and it goes until
 * a figure of this compiler's stops it, at which point what the search has to say is that it
 * stopped. Which is what a reader is then told: raise the figure. Raising it walks further into the
 * same nothing.
 *
 * <p>The proof was there before any value was chosen. What makes it worth saying is that a reader
 * may act on it and may act on none of the figures (ADR-0091), so it has to arrive as itself rather
 * than as one more thing this compiler did not manage.
 *
 * <p>Each search is put beside the same question asked of a region that merely narrows nothing,
 * because the two regions answer every question about where a form runs with neither end. A check
 * that read the ends could not tell them apart, which is the shape of the defect rather than a
 * detail of it.
 */
class ARegionShownToHoldNothingIsNotWalkedTest {

    /** A position of whole numbers, which is a run wider than any walk here looks at. */
    private static final NumericTerm.FromOnePosition WIDE =
            new NumericTerm.ValueOf(TermPath.of("p.x"));

    /** A second position no order answers, so nothing tried at the first leads anywhere. */
    private static final NumericTerm.FromOnePosition NOWHERE =
            new NumericTerm.ValueOf(TermPath.of("p.y"));

    private static final TermOrders WHOLE =
            TermOrdersFixtures.itself(WIDE, new Carrier.Whole());

    private static NumericWitness.Standing witnessIn(
            souther.compiler.inputs.SearchRegion within) {
        return NumericWitness.of(within, List.of(WIDE, NOWHERE),
                term -> term == NOWHERE ? null : Carrier.WHOLE,
                NothingTheDeclarationsNarrow.LOOKING);
    }

    private static Realization realizedIn(souther.compiler.inputs.SearchRegion within) {
        Standing standing = new BorderQuantity.OverAForm("decide",
                LinearForm.atom((NumericTerm) WIDE), Map.of(WIDE, WHOLE))
                .standingAt(new Criterion.AtTheLevel(new Level.ACount(Count.of(4))));
        return new LevelRealizer().realize(standing, within, NothingTheDeclarationsRefuse.at());
    }

    /** The condition on the way is answered by the rules, and no value is tried for it. */
    @Test
    void theWitnessComesBackWithTheProofAndSpendsNothing() {
        assertInstanceOf(NumericWitness.Standing.ProvedImpossible.class,
                witnessIn(NothingTheRulesLeave.REGION),
                "the rules were shown to leave the region nothing, so nothing was walked in it");
    }

    /**
     * And the same question of a region that narrows nothing spends one.
     *
     * <p>The control. Both regions leave every form neither end, and only one of them is a proof —
     * so what tells them apart here is that this one walks until it runs out and the other one never
     * starts.
     */
    @Test
    void theSameQuestionOfARegionThatNarrowsNothingStopsAtAFigure() {
        assertEquals(Set.of(CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT),
                assertInstanceOf(NumericWitness.Standing.NotFound.class,
                        witnessIn(NothingTheRulesSay.REGION),
                        "nothing was shown empty, so nothing is proved about the pair").stoppedBy(),
                "and what it came back with is the figure it stopped at");
    }

    /**
     * A position the rules leave nothing is the model's answer as much as a region that holds
     * nothing is.
     *
     * <p>The pair the region above cannot tell apart, because it answers both questions the same
     * way. Here the region stands and one position of it has nowhere to be — an input holding an
     * empty collection against a position inside that collection — and what a reader is owed is
     * still the proof rather than a figure to raise.
     */
    @Test
    void aPositionWithNowhereToStandIsTheProofTooEvenWhereTheRegionStands() {
        assertInstanceOf(NumericWitness.Standing.ProvedImpossible.class,
                witnessIn(OnePositionTheRulesLeaveNothing.leaving(WIDE)),
                "the region admits an assignment and this position is at no value in it");
    }

    /** A point of a border is settled by the rules too, before a level of it is asked for. */
    @Test
    void theRealizerComesBackWithTheProofAndSpendsNothing() {
        assertEquals(new Realization.Impossible(), realizedIn(NothingTheRulesLeave.REGION),
                "the rules leave nothing at the item, which is what a reader may act on");
    }

    /** And of a region that narrows nothing it is a search like any other. */
    @Test
    void theSameItemInARegionThatNarrowsNothingIsSearchedFor() {
        assertNotEquals(new Realization.Impossible(), realizedIn(NothingTheRulesSay.REGION),
                "nothing was shown empty, so nothing about the item is settled by the rules");
    }

    /** And a position of the item with nowhere to stand settles it as surely. */
    @Test
    void aPositionOfTheItemWithNowhereToStandSettlesItToo() {
        assertEquals(new Realization.Impossible(),
                realizedIn(OnePositionTheRulesLeaveNothing.leaving(WIDE)),
                "the region admits an assignment and the item's position is at no value in it");
    }

    /**
     * A form the rules leave nowhere settles the item, though every position of it stands.
     *
     * <p>The question a per-position reading cannot put. What a rule over two positions leaves is a
     * fact about their sum, and each of them running somewhere says nothing about whether the sum
     * does — so an item over a form that asked its positions one at a time would walk a form the
     * rules have already refused, and come back naming a figure.
     */
    @Test
    void aFormTheRulesLeaveNowhereSettlesTheItemThoughItsPositionsStand() {
        Standing standing = new BorderQuantity.OverAForm("decide",
                LinearForm.atom((NumericTerm) WIDE).plus(LinearForm.atom((NumericTerm) NOWHERE)),
                Map.of(WIDE, WHOLE,
                        NOWHERE, TermOrdersFixtures.itself(NOWHERE, new Carrier.Whole())))
                .standingAt(new Criterion.AtTheLevel(new Level.ACount(Count.of(4))));

        assertEquals(new Realization.Impossible(),
                new LevelRealizer().realize(standing, EveryPositionStandsAndTheirSumDoesNot.REGION,
                        NothingTheDeclarationsRefuse.at()),
                "the form is what the rules refuse, and each of its positions runs somewhere");
    }

    /**
     * A position left nothing by the value the walk fixed above it ends that branch, and does not
     * end the search.
     *
     * <p>The case an entry check cannot reach. Nothing here is empty when the search is handed it:
     * the walk makes it so by choosing a value, and what the rules then leave is a fact about that
     * choice. So the branch is exhausted — a proof of its own, and the walk goes on to the values
     * beside it.
     *
     * <p>What this pins first is that it comes back at all. Read for a range, a position at no value
     * is an answer that is not one, and the reader that met it had nowhere to put it.
     */
    @Test
    void aPositionLeftNothingByAFixingEndsThatBranchAndNotTheSearch() {
        Standing standing = new BorderQuantity.OverAForm("decide",
                LinearForm.atom((NumericTerm) WIDE).plus(LinearForm.atom((NumericTerm) NOWHERE)),
                Map.of(WIDE, WHOLE, NOWHERE, TermOrdersFixtures.itself(NOWHERE, new Carrier.Whole())))
                .standingAt(new Criterion.AtTheLevel(new Level.ACount(Count.of(4))));

        Realization made = new LevelRealizer().realize(standing,
                APositionLeftNothingOnlyOnceAnotherIsFixed.of(WIDE, NOWHERE),
                NothingTheDeclarationsRefuse.at());

        assertEquals(new Realization.Impossible(), made,
                "every value of the first leaves the second nothing, so every branch is a proof and"
                        + " the walk of a point that reached none of them is one too");
    }
}
