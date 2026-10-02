package souther.test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How a count grows from one size to the next, for a test that holds a cost by a counter the code
 * keeps while the test asks.
 *
 * <p>A bound on growth holds of a count that never counted: nothing at each size is no more than
 * any multiple of nothing. So a count of nothing is refused before the growth is asked about — the
 * sizes a test measures do the work being counted, and a counter that saw none of it is not
 * counting, which is the one state a test of a cost has to tell apart from a cost that did not grow.
 */
public final class Growth {

    private Growth() {}

    /**
     * That each count in {@code bySize}, taken in the order the map holds them, is at most
     * {@code times / per} the one before it, and that none of them is nothing.
     */
    public static void eachAtMost(SequencedMap<Integer, Long> bySize, long times, long per) {
        List<Map.Entry<Integer, Long>> inOrder = new ArrayList<>(counted(bySize).entrySet());
        for (int i = 1; i < inOrder.size(); i++) {
            long before = inOrder.get(i - 1).getValue();
            long after = inOrder.get(i).getValue();
            assertTrue(after * per <= before * times, "from " + inOrder.get(i - 1).getKey()
                    + " to " + inOrder.get(i).getKey() + " the count grew more than " + times
                    + "/" + per + ": " + bySize);
        }
    }

    /**
     * {@code bySize}, once none of its counts is nothing — for a test asking something of the counts
     * other than how each grows from the last.
     */
    public static <M extends Map<Integer, Long>> M counted(M bySize) {
        for (Map.Entry<Integer, Long> each : bySize.entrySet()) {
            assertTrue(each.getValue() > 0, "nothing was counted at " + each.getKey()
                    + ", so the counter is not counting: " + bySize);
        }
        return bySize;
    }
}
