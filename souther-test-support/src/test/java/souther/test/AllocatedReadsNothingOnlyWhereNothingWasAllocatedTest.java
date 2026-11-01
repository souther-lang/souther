package souther.test;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A test that holds work to allocating nothing passes on a reading of nothing, so the reading has
 * to be of a counter that counts: work that allocates reads as what it allocated, and work that does
 * not reads as nothing.
 */
class AllocatedReadsNothingOnlyWhereNothingWasAllocatedTest {

    private static volatile Object sink;

    @Test
    void workThatAllocatesReadsAsAtLeastWhatItAllocated() {
        long allocated = Allocated.byWhichMayBeNothing(() -> sink = new byte[100_000]);
        assertTrue(allocated >= 100_000, "an array of 100000 bytes was read as " + allocated);
    }

    @Test
    void workThatAllocatesNothingReadsAsNothing() {
        Runnable noWork = () -> { };
        noWork.run();
        assertEquals(0, Allocated.byWhichMayBeNothing(noWork));
    }
}
