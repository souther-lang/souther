package souther.runtime;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;

/**
 * An allocation budget for {@link PersistentVector#append}, the operation every fold-derived
 * combinator grows its list with ({@code acc ++ [x]} → {@link Lists#append}).
 *
 * <p>This asserts bytes allocated per element rather than elapsed time. Allocation is counted
 * exactly by the JVM, so the number is stable across machines and load in a way a timing benchmark
 * is not, and the test can carry a real assertion instead of being disabled. The loop appends the
 * same pre-made {@code Object} rather than a boxed number so the measurement isolates the vector's
 * own cost: nothing in it is escape-analyzable either way, which is why the bound can be tight.
 *
 * <p>Measured on GraalVM 25.0.3 and Zulu 21.0.9 (arm64), 200k appends, fourth run after three
 * discarded:
 *
 * <pre>
 *                                            before   after
 *   append, same Object (asserted here)     128 B/e   50 B/e
 *   Lists.append, i.e. what `acc ++ [x]`    144 B/e   66 B/e   [HotSpot 21]
 *   emits (context)                         112 B/e   38 B/e   [GraalVM 25]
 *   List.map through a behavior (context)   160 B/e  106 B/e   [HotSpot 21]
 *                                           112 B/e   66 B/e   [GraalVM 25]
 * </pre>
 *
 * <p>The "before" column is the exactly-sized tail that was copied on every append; the "after"
 * column is the claimed tail (see {@link PersistentVector}'s class javadoc and ADR-0060). Only the
 * first row is measured here; the others need the compiler and are recorded for context.
 *
 * <p>Every figure above is with compressed oops. Without them (a max heap of 32 GB or more turns
 * them off) references are 8 bytes instead of 4 and the same code costs 73 B/element, which is what
 * the budget below has to leave room for.
 *
 * <p>Re-run: {@code mvn -pl souther-runtime test -Dtest=PersistentVectorAllocationTest}
 */
class PersistentVectorAllocationTest {

    /** Above the tail width many times over, so the per-element cost is the steady state and not
     *  the first block. */
    private static final int ELEMENTS = 200_000;

    /**
     * Above the claimed tail's cost on either object layout — 50 B/element with compressed oops, 73
     * without — and well below the 128 the copying tail cost, so going back to copying fails the
     * test while a machine with a large heap does not.
     */
    private static final long MAX_BYTES_PER_ELEMENT = 100;

    @Test
    void appendStaysWithinItsAllocationBudget() {
        com.sun.management.ThreadMXBean bean = allocationCountingBean();

        for (int warmup = 0; warmup < 3; warmup++) {
            grow();
        }

        long before = bean.getCurrentThreadAllocatedBytes();
        PersistentVector<Object> built = grow();
        long after = bean.getCurrentThreadAllocatedBytes();

        long perElement = (after - before) / ELEMENTS;
        System.out.println("PersistentVector.append: " + perElement + " bytes/element");
        assertTrue(perElement > 0, "allocation accounting reported nothing; measurement is broken");
        assertTrue(perElement < MAX_BYTES_PER_ELEMENT,
                "append allocated " + perElement + " bytes/element, budget is "
                        + MAX_BYTES_PER_ELEMENT);
        assertTrue(built.size() == ELEMENTS, "the built vector was optimized away");
    }

    private static PersistentVector<Object> grow() {
        Object element = new Object();
        PersistentVector<Object> pv = PersistentVector.empty();
        for (int i = 0; i < ELEMENTS; i++) {
            pv = pv.append(element);
        }
        return pv;
    }

    /** The allocation counter, or a skipped test where the JVM does not offer one. */
    private static com.sun.management.ThreadMXBean allocationCountingBean() {
        ThreadMXBean threads = ManagementFactory.getThreadMXBean();
        Assumptions.assumeTrue(threads instanceof com.sun.management.ThreadMXBean,
                "this JVM has no com.sun.management.ThreadMXBean");
        com.sun.management.ThreadMXBean bean = (com.sun.management.ThreadMXBean) threads;
        Assumptions.assumeTrue(bean.isThreadAllocatedMemorySupported(),
                "this JVM does not support per-thread allocation counting");
        bean.setThreadAllocatedMemoryEnabled(true);
        return bean;
    }
}
