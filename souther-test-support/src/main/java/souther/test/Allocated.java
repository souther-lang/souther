package souther.test;

import org.junit.jupiter.api.Assumptions;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;

/**
 * What a piece of work allocates on the thread that runs it, for a test that holds a cost by it.
 *
 * <p>Allocation is the same each run whatever else the machine is doing, which time is not, so it is
 * what a test of a cost can read. But the counter is the JVM's to offer: where it has none, or has
 * one switched off, it answers a figure that is no measurement — and a difference of two of those is
 * nothing allocated, which is the one answer a test of a cost passes on. So the counter is asked for
 * and switched on here, a JVM without one skips the test rather than passing it, and a reading of
 * nothing is refused rather than handed back: the work a test measures allocates something, and a
 * counter that saw none of it is not counting.
 */
public final class Allocated {

    private Allocated() {}

    /** What running {@code work} allocated on this thread, in bytes. */
    public static long by(Runnable work) {
        com.sun.management.ThreadMXBean counter = counter();
        long before = counter.getCurrentThreadAllocatedBytes();
        work.run();
        long allocated = counter.getCurrentThreadAllocatedBytes() - before;
        if (allocated <= 0) {
            throw new AssertionError("the allocation counter reported " + allocated
                    + " bytes for work that allocates, so it is not counting");
        }
        return allocated;
    }

    /**
     * What running {@code work} allocated on this thread, in bytes, where it may allocate nothing.
     *
     * <p>For a test that holds a cost to nothing at all, or to a bound. A reading of nothing is then
     * the answer the test wants, so it cannot be told from a counter that counts nothing by the
     * reading; the counter is asked to count an allocation of known size first.
     */
    public static long byWhichMayBeNothing(Runnable work) {
        com.sun.management.ThreadMXBean counter = counter();
        long calibrationStart = counter.getCurrentThreadAllocatedBytes();
        calibration = new byte[CALIBRATION_BYTES];
        long counted = counter.getCurrentThreadAllocatedBytes() - calibrationStart;
        if (counted < calibration.length) {
            throw new AssertionError("the allocation counter reported " + counted + " bytes for an array of "
                    + calibration.length + ", so it is not counting");
        }
        long before = counter.getCurrentThreadAllocatedBytes();
        work.run();
        return counter.getCurrentThreadAllocatedBytes() - before;
    }

    private static final int CALIBRATION_BYTES = 4096;

    /** Where the calibration array goes, so that it is not an allocation the JIT may leave out. */
    private static volatile byte[] calibration;

    private static com.sun.management.ThreadMXBean counter() {
        ThreadMXBean threads = ManagementFactory.getThreadMXBean();
        Assumptions.assumeTrue(threads instanceof com.sun.management.ThreadMXBean,
                "this JVM has no com.sun.management.ThreadMXBean");
        com.sun.management.ThreadMXBean counter = (com.sun.management.ThreadMXBean) threads;
        Assumptions.assumeTrue(counter.isThreadAllocatedMemorySupported(),
                "this JVM does not count what a thread allocates");
        if (!counter.isThreadAllocatedMemoryEnabled()) {
            counter.setThreadAllocatedMemoryEnabled(true);
        }
        return counter;
    }
}
