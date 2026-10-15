package souther.runtime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.LinkedHashMap;
import java.util.Map;
import org.junit.jupiter.api.Test;
import souther.test.Allocated;

/**
 * An allocation budget for bulk construction of a {@link PersistentHashMap}, the path every decoded
 * {@code Map} or {@code Set} field takes, along with {@code Map.fromList}, {@code Set.fromList},
 * {@code Set.map}/{@code filter} (which route through {@code toList}/{@code fromList}) and the set
 * algebra.
 *
 * <p>Like {@link PersistentVectorAllocationTest} this asserts bytes allocated rather than elapsed
 * time, so the number is stable enough to carry a real assertion. Measured on GraalVM 25.0.3
 * (arm64), 1000 entries, after warm-up:
 *
 * <pre>
 *                                          before   after
 *   PersistentHashMap.from (asserted)      406 B/e   167 B/e
 *   PersistentHashSet.from (context)       415 B/e   164 B/e
 *   assoc one at a time (unchanged)        357 B/e   357 B/e
 * </pre>
 *
 * <p>The last row is the point of the design: the builder must not cost the persistent path
 * anything, which is why ownership is a flag threaded down the call rather than a mark on each node.
 * The element-wise figure stays where it was because a persistent {@code assoc} still clones every
 * node on the path — it has to, and no runtime check can change that (ADR-0061).
 *
 * <p>Re-run: {@code mvn -pl souther-runtime test -Dtest=PersistentHashMapAllocationTest}
 */
class PersistentHashMapAllocationTest {

    /** Two full trie levels, so the per-entry cost is the steady state rather than the first node. */
    private static final int ENTRIES = 1000;

    /** Between the measured 167 after and the 406 before, with room either side for a different
     *  object layout (a JVM without compressed oops allocates more for the same code). */
    private static final long MAX_BYTES_PER_ENTRY = 280;

    @Test
    void bulkConstructionStaysWithinItsAllocationBudget() {
        Map<Object, Object> source = new LinkedHashMap<>();
        for (int i = 0; i < ENTRIES; i++) {
            source.put("k" + i, i);
        }

        for (int warmup = 0; warmup < 3; warmup++) {
            PersistentHashMap.from(source);
        }

        long perEntry = Allocated.by(
                () -> assertEquals(ENTRIES, PersistentHashMap.from(source).size())) / ENTRIES;
        assertTrue(perEntry < MAX_BYTES_PER_ENTRY,
                "from allocated " + perEntry + " bytes/entry, budget is " + MAX_BYTES_PER_ENTRY);
    }
}
