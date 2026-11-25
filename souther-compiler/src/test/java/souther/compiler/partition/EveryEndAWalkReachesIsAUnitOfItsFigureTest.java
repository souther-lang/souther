package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A walk's figure counts every end it reaches, the dead ends as well as the whole ways, and so
 * bounds the states the walk enters.
 *
 * <p>The search is three positions of ten choices each, where nothing is left to choose at the
 * last one: no whole way at all, and a dead end after each of the hundred ways of the first two.
 * Counted at the whole ways alone, the walk would go through all hundred and spend nothing.
 */
class EveryEndAWalkReachesIsAUnitOfItsFigureTest {

    private static final int WIDE = 10;

    @Test
    void aWalkWhoseLastChoicesAllFallAwaySpendsAUnitAtEachDeadEnd() {
        Counted exactly = walked(WIDE * WIDE, true);
        assertEquals(DepthFirst.Walked.EVERY_END_REACHED, exactly.walked());
        assertFalse(exactly.tries().cutShort(), "the last unit went to the last end");
        assertEquals(DepthFirst.Walked.CUT_SHORT, walked(WIDE * WIDE - 1, true).walked());
    }

    /** Every state entered is on the way to an end, so a figure of five ends enters no more than
     *  the three positions' worth of states for each of them and the one it stopped at. */
    @Test
    void theStatesAWalkEntersAreBoundedByTheEndsItsFigureAllows() {
        Counted cut = walked(5, true);
        assertEquals(DepthFirst.Walked.CUT_SHORT, cut.walked());
        assertTrue(cut.entered() <= 3 * (5 + 1), () -> cut.entered() + " states entered");
    }

    @Test
    void aWholeWayIsAUnitAndAWayTakenEndsTheWalk() {
        Counted taken = walked(1, false);
        assertEquals(DepthFirst.Walked.TAKEN, taken.walked());
        assertFalse(taken.tries().cutShort());
    }

    private record Counted(DepthFirst.Walked walked, Tries tries, int entered) {}

    /** The walk at {@code figure}: the last position left nothing where {@code emptyAtTheEnd},
     *  and every way taken where not. */
    private static Counted walked(int figure, boolean emptyAtTheEnd) {
        Tries tries = new Tries(figure);
        int[] entered = {0};
        DepthFirst.Walked walked = DepthFirst.walk(0, tries, depth -> {
            entered[0]++;
            if (depth == 3) {
                return null;
            }
            if (depth == 2 && emptyAtTheEnd) {
                return List.of();
            }
            return IntStream.range(0, WIDE).mapToObj(_ -> depth + 1).toList();
        }, way -> false);
        return new Counted(walked, tries, entered[0]);
    }
}
