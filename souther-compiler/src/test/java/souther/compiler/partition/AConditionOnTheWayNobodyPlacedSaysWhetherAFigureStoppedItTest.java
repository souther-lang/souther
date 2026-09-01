package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition on the way that nothing placed says whether a figure of this compiler's stopped the
 * placing.
 *
 * <p>A row is composed either way, and what the condition costs is that the row was not composed
 * against it — so this is not a point nothing could be established at, and it is not nothing either.
 * A reader told only that no value was composed for the condition's positions cannot tell a walk
 * that tried what it had from one that stopped at a number, and only the second names something
 * anybody could raise.
 *
 * <p>Held here rather than against a model. The walk stops at eight values of a position, and a
 * model that reaches that has to leave a condition over two positions where the first has more than
 * eight values the second refuses — which is a model about the arithmetic rather than about this.
 * At this end the walk is put one either side of its own figure.
 */
class AConditionOnTheWayNobodyPlacedSaysWhetherAFigureStoppedItTest {

    /** A position of whole numbers, which is a run wider than the walk looks at. */
    private static final NumericTerm.FromOnePosition WIDE =
            new NumericTerm.ValueOf(TermPath.of("p.x"));

    /** A second position the walk has no order for, so nothing it tries at the first leads
     *  anywhere. */
    private static final NumericTerm.FromOnePosition NOWHERE =
            new NumericTerm.ValueOf(TermPath.of("p.y"));

    /**
     * A walk that ran out of the values it looks at says which figure it stopped at.
     *
     * <p>The far side of the line. Every value of the first position leads nowhere, so the walk
     * tries as many as it looks at and comes back with nothing — and what it comes back with is
     * that a figure of this compiler's is why, rather than that the positions have no values.
     */
    @Test
    void aWalkThatRanOutOfWhatItLooksAtNamesTheFigure() {
        NumericWitness.Standing standing = NumericWitness.of(NothingTheRulesSay.REGION,
                List.of(WIDE, NOWHERE), term -> term == NOWHERE ? null : Carrier.WHOLE);

        assertNull(standing.at(), "the second position has no order, so no pair stands anywhere");
        assertEquals(Set.of(CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT),
                standing.stoppedBy(),
                "and the walk stopped at how many values a position on the way is tried at");
    }

    /**
     * A walk that had nothing to try names no figure.
     *
     * <p>The near side. A position with no order was never walked, so nothing was cut short — and
     * saying a figure stopped it would name a budget nobody reached.
     */
    @Test
    void aWalkWithNothingToTryNamesNoFigure() {
        NumericWitness.Standing standing = NumericWitness.of(NothingTheRulesSay.REGION,
                List.of(NOWHERE), _ -> null);

        assertNull(standing.at(), "there is nothing for the position to stand on");
        assertEquals(Set.of(), standing.stoppedBy(),
                "and nothing was stopped, which is not the same as having been stopped by nothing");
    }

    /** And a walk that found somewhere for every position says neither. */
    @Test
    void aWalkThatFoundSomewhereNamesNoFigure() {
        NumericWitness.Standing standing = NumericWitness.of(NothingTheRulesSay.REGION,
                List.of(WIDE), _ -> Carrier.WHOLE);

        assertNotNull(standing.at(), "a whole number stands somewhere in a region nothing narrows");
        assertTrue(standing.stoppedBy().isEmpty(), "so no figure was reached on the way");
    }

    /**
     * What such a walk hands the row's account, which is a condition it was not composed against and
     * not a point nothing could be established at.
     */
    @Test
    void whatItHandsOverIsAConditionAndNeverAPointNothingWasComposedFor() {
        ReachabilityGap.Why why = new ReachabilityGap.Why.TheWalkForItsPositionsWasStopped(
                Set.of(CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT));

        assertEquals(Set.of(CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT),
                ((ReachabilityGap.Why.TheWalkForItsPositionsWasStopped) why).by(),
                "the figure travels as itself, so a reader can be told which one to raise");
    }

}
