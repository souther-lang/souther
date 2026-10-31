package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way read again for a relation is read with no more walks than
 * {@link CompositionBudget#WALKS_A_WAY_IS_READ_AGAIN_WITH}, and where that leaves the relation
 * shown nothing, it says the figure is one of the reasons why.
 *
 * <p>Choices whose way apart is met come first, and choices whose way apart is not come after
 * them ({@link WaysReadAgain}). Each choice kept as it stands sends the reading back to the
 * first, and finding the next one to keep is walks of its own, so the walks run out before the
 * last of them is found. Which figure a relation names is read off what the reading again says,
 * and how a reader is told it is asked of models in
 * {@code ARelationLeavesAPlaceUndividedOnlyWhereTheOtherSideIsShownToReachItTest}; what this asks
 * is that the walks are counted and the count said.
 */
class AWayReadAgainPastItsWalksSaysSoTest {

    @Test
    void aReadingAgainThatRunsOutOfWalksSaysSo() {
        List<OnTheWay> way = new ArrayList<>(WaysReadAgain.met(20, 0));
        way.addAll(WaysReadAgain.notMet(60, 20));

        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(way);

        assertTrue(again.stoppedAt().contains(CompositionBudget.WALKS_A_WAY_IS_READ_AGAIN_WITH),
                () -> "the walks ran out, and say so: " + again);
        assertTrue(again.as().isEmpty(), "and nothing is read as less past them");
    }
}
