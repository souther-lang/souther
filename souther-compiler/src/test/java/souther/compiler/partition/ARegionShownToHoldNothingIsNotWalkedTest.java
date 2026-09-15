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
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

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
                term -> term == NOWHERE ? null : Carrier.WHOLE);
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
        NumericWitness.Standing standing = witnessIn(NothingTheRulesLeave.REGION);

        assertTrue(standing.provedEmpty(), "the rules were shown to leave the region nothing");
        assertNull(standing.at(), "so no pair stands anywhere in it");
        assertEquals(Set.of(), standing.stoppedBy(),
                "and no figure of this compiler's was spent finding that out");
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
        NumericWitness.Standing standing = witnessIn(NothingTheRulesSay.REGION);

        assertEquals(false, standing.provedEmpty(),
                "nothing was shown empty, so nothing is proved about the pair");
        assertEquals(Set.of(CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT),
                standing.stoppedBy(),
                "and what it came back with is the figure it stopped at");
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
}
