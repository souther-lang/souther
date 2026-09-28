package souther.runtime;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link Sorting} sorts in chunks, by merging runs, so that a list longer than an array still
 * sorts. What it answers is held against the host's own stable sort on the same input, with many
 * equal keys so that stability is what decides the order, and at lengths either side of a run and
 * across the boundary between two chunks.
 */
class ASortOverChunksIsTheStableSortTest {

    /** An element carrying the key it is ordered by and where it stood, so an equal pair's order is
     *  something the comparison can see. */
    private record Keyed(int key, int at) {}

    @Test
    void theChunkedSortIsTheHostsStableSort() {
        Random random = new Random(1985);
        for (int n : new int[] {0, 1, 2, 31, 32, 33, 64, 1000, 65_535, 65_536, 65_537, 200_003}) {
            List<Keyed> xs = new ArrayList<>(n);
            for (int i = 0; i < n; i++) {
                xs.add(new Keyed(random.nextInt(50), i));
            }
            Comparator<Keyed> byKey = Comparator.comparingInt(Keyed::key);
            List<Keyed> expected = new ArrayList<>(xs);
            expected.sort(byKey);
            assertEquals(expected, Sorting.stably(xs, byKey), "n = " + n);
        }
    }

    /** A sort leaves what it was handed as it was. */
    @Test
    void theInputIsLeftAsItWas() {
        List<Integer> xs = List.of(3, 1, 2);
        assertEquals(List.of(1, 2, 3), Sorting.stably(xs, Comparator.naturalOrder()));
        assertEquals(List.of(3, 1, 2), xs);
    }
}
