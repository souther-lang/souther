package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way read again for a relation finds the choice it keeps whole by halving the choices, and not
 * by asking one choice more at a time.
 *
 * <p>Asked one more at a time, each choice is a walk of the way with every choice before it, so
 * the walks are as many as the choices. Here more choices are met than a way is read again with
 * walks ({@link CompositionBudget#WALKS_A_WAY_IS_READ_AGAIN_WITH}); halved, they are as many walks
 * as their logarithm, whether every one is met or the last is not ({@link WaysReadAgain}).
 */
class AWayReadAgainFindsTheChoiceToKeepWholeByHalvingTest {

    private static final int MET = CompositionBudget.WALKS_A_WAY_IS_READ_AGAIN_WITH.maximum() + 1;

    /** Every choice met: asked of all of them at once, and read as less. */
    @Test
    void choicesAllMetAreReadAsLessWithoutRunningOutOfWalks() {
        readAsLessWithoutRunningOut(WaysReadAgain.met(MET, 0));
    }

    /** The last choice not met: the halving finds it, it is kept whole, and the rest are read as
     *  less. */
    @Test
    void theOneChoiceNotMetIsFoundWithoutRunningOutOfWalks() {
        List<OnTheWay> way = new ArrayList<>(WaysReadAgain.met(MET, 0));
        way.addAll(WaysReadAgain.notMet(1, MET));
        readAsLessWithoutRunningOut(way);
    }

    private static void readAsLessWithoutRunningOut(List<OnTheWay> way) {
        AWayReadForARelation.ReadAgain again = WaysReadAgain.readAgain(way);

        assertFalse(again.stoppedAt().contains(CompositionBudget.WALKS_A_WAY_IS_READ_AGAIN_WITH),
                () -> "the walks did not run out: " + again.stoppedAt());
        assertTrue(again.as().isPresent(), "and the way is read as less for the relation");
    }
}
