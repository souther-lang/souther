package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredBounds;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A grouping of leaves into the containers of every level that was made, and a grouping the room
 * turned away, are two facts a count of leaves comes to, and each is carried.
 *
 * <p>Held apart because a reader told only that a row was built takes the offer for everything
 * there was, and one told only that the room refused something takes the offer for nothing. The
 * groupings written are two, the leaves shared evenly and the leaves loaded on the first, and the
 * room can have no place for one of them and room enough for the other.
 */
class ACountOfLeavesTheRoomTurnedAwayIsSaidBesideTheGroupingsMadeTest {

    private static List<DeclaredBounds.CountRange> counts(int... mosts) {
        return java.util.Arrays.stream(mosts)
                .mapToObj(most -> new DeclaredBounds.CountRange(0, most)).toList();
    }

    /**
     * Lists of at most eight, of at most two, of at most eight, and fifty-three leaves: shared
     * evenly they take sixty-five elements, past the room of sixty-four, and loaded on the first
     * they take sixty-four.
     */
    @Test
    void aGroupingThatFitsIsMadeAndTheOneThatDidNotIsSaidToBeRefused() {
        NestedContainersAddingUp.Groupings groupings =
                NestedContainersAddingUp.groupingsOf(counts(8, 2, 8), 53, null, 64);

        assertFalse(groupings.made().isEmpty(), "the grouping that takes sixty-four is made");
        assertTrue(groupings.made().stream().allMatch(each -> each.elements() <= 64),
                "and none past the room");
        assertTrue(groupings.refused(), "the one that takes sixty-five was in front of the walk");
    }

    /** A count every grouping fits in turns nothing away. */
    @Test
    void groupingsThatAllFitRefuseNothing() {
        NestedContainersAddingUp.Groupings groupings =
                NestedContainersAddingUp.groupingsOf(counts(8, 2, 8), 6, null, 64);

        assertFalse(groupings.made().isEmpty());
        assertFalse(groupings.refused());
    }

    /** A count the levels leave no grouping for says nothing of the room. */
    @Test
    void aCountNoGroupingMeetsIsNotARefusal() {
        // Lists of exactly two leaves in lists of at most one: one leaf is no grouping at all.
        NestedContainersAddingUp.Groupings groupings = NestedContainersAddingUp.groupingsOf(
                List.of(new DeclaredBounds.CountRange(0, 70),
                        new DeclaredBounds.CountRange(0, 1),
                        new DeclaredBounds.CountRange(2, 2)), 1, null, 64);

        assertEquals(List.of(), groupings.made());
    }
}
