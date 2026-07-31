package souther.runtime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import org.junit.jupiter.api.Test;

/** {@link PersistentVector} against an {@link ArrayList} oracle, across sizes that span several trie
 *  depths (tail boundary 32, root overflow, and multi-level tries). */
class PersistentVectorTest {

    private static final int[] SIZES = {0, 1, 31, 32, 33, 63, 64, 65, 1023, 1024, 1025, 100_000};

    @Test
    void appendGetSizeMatchArrayList() {
        for (int n : SIZES) {
            List<Integer> oracle = new ArrayList<>();
            PersistentVector<Integer> pv = PersistentVector.empty();
            for (int i = 0; i < n; i++) {
                oracle.add(i);
                pv = pv.append(i);
            }
            assertEquals(n, pv.size(), "size at n=" + n);
            for (int i = 0; i < n; i++) {
                assertEquals(oracle.get(i), pv.get(i), "get(" + i + ") at n=" + n);
            }
        }
    }

    @Test
    void iteratorAndForEachAreInOrder() {
        for (int n : SIZES) {
            PersistentVector<Integer> pv = PersistentVector.empty();
            for (int i = 0; i < n; i++) {
                pv = pv.append(i);
            }
            int expected = 0;
            for (Integer v : pv) {
                assertEquals(expected++, v);
            }
            assertEquals(n, expected);

            int[] seen = {0};
            pv.forEach(v -> assertEquals(seen[0]++, v));
            assertEquals(n, seen[0]);
        }
    }

    @Test
    void appendedVersionsAreIndependent() {
        PersistentVector<Integer> a = PersistentVector.empty();
        for (int i = 0; i < 40; i++) {
            a = a.append(i);
        }
        PersistentVector<Integer> b = a.append(999);
        PersistentVector<Integer> aFinal = a;
        assertEquals(40, aFinal.size());
        assertEquals(41, b.size());
        assertEquals(999, b.get(40));
        assertThrows(IndexOutOfBoundsException.class, () -> aFinal.get(40));
    }

    @Test
    void fromSharesPersistentAndCopiesJdkLists() {
        PersistentVector<Integer> pv = PersistentVector.<Integer>empty().append(1).append(2);
        assertTrue(PersistentVector.from(pv) == pv, "from must share an existing PersistentVector");

        List<Integer> jdk = List.of(1, 2, 3, 33, 34);
        PersistentVector<Integer> copy = PersistentVector.from(jdk);
        assertEquals(jdk, copy);
        assertEquals(5, copy.size());
        assertTrue(PersistentVector.from(List.of()) == PersistentVector.EMPTY);
    }

    @Test
    void fromBuildsSameVectorAsAppendAcrossDepths() {
        for (int n : SIZES) {
            List<Integer> oracle = new ArrayList<>();
            for (int i = 0; i < n; i++) {
                oracle.add(i);
            }
            // from() uses the bulk Builder; it must produce a vector identical to element-wise append.
            PersistentVector<Integer> viaBuilder = PersistentVector.from(oracle);
            PersistentVector<Integer> viaAppend = PersistentVector.empty();
            for (int i = 0; i < n; i++) {
                viaAppend = viaAppend.append(i);
            }
            assertEquals(n, viaBuilder.size(), "size at n=" + n);
            assertEquals(oracle, viaBuilder, "equals oracle at n=" + n);
            assertEquals(viaAppend, viaBuilder, "builder vs append at n=" + n);
            for (int i = 0; i < n; i++) {
                assertEquals(i, viaBuilder.get(i), "get(" + i + ") at n=" + n);
            }
            int expected = 0;
            for (Integer v : viaBuilder) {
                assertEquals(expected++, v);
            }
            assertEquals(n, expected);
        }
    }

    /** Successive appends share one tail array, so every intermediate version has to keep reading
     *  only its own prefix even after longer versions have written past it. */
    @Test
    void everyIntermediateVersionStaysIntact() {
        for (int n : SIZES) {
            List<PersistentVector<Integer>> versions = versions(n);
            for (int v = 0; v <= n; v++) {
                PersistentVector<Integer> version = versions.get(v);
                assertEquals(v, version.size());
                // Only the live tail can be written past, and it is the last WIDTH slots at most;
                // everything below tailoff is a frozen trie leaf. Checking that window instead of
                // the whole prefix keeps this linear, so every version can be checked rather than a
                // sample of them.
                for (int i = Math.max(0, v - 33); i < v; i++) {
                    if (version.get(i) != i) {
                        fail("version " + v + " at n=" + n + " reads " + version.get(i)
                                + " at index " + i);
                    }
                }
                assertThrows(IndexOutOfBoundsException.class, () -> version.get(version.size()));
            }
        }
    }

    /** {@code 0..n-1} appended one at a time, keeping every version — index {@code v} holds the
     *  first {@code v} elements. */
    private static List<PersistentVector<Integer>> versions(int n) {
        List<PersistentVector<Integer>> versions = new ArrayList<>();
        PersistentVector<Integer> pv = PersistentVector.empty();
        versions.add(pv);
        for (int i = 0; i < n; i++) {
            pv = pv.append(i);
            versions.add(pv);
        }
        return versions;
    }

    /** Only the first append off a version extends the shared tail in place; a second one has to
     *  copy. Both results, and the version they branched from, must be right. */
    @Test
    void branchingOffEveryPrefixKeepsAllThreeCorrect() {
        int n = 1030;   // spans the tail boundary at 32 and the root overflow at 1024
        List<PersistentVector<Integer>> versions = versions(n);
        for (int v = 0; v <= n; v++) {
            PersistentVector<Integer> base = versions.get(v);
            PersistentVector<Integer> left = base.append(-1);
            PersistentVector<Integer> right = base.append(-2);
            assertEquals(v, base.size());
            assertEquals(v + 1, left.size());
            assertEquals(v + 1, right.size());
            assertEquals(-1, left.get(v), "left branch off version " + v);
            assertEquals(-2, right.get(v), "right branch off version " + v);
            // Same window as everyIntermediateVersionStaysIntact, and for the same reason.
            for (int i = Math.max(0, v - 33); i < v; i++) {
                if (base.get(i) != i || left.get(i) != i || right.get(i) != i) {
                    fail("branching off version " + v + " disturbed index " + i
                            + ": base=" + base.get(i) + " left=" + left.get(i)
                            + " right=" + right.get(i));
                }
            }
        }
    }

    /** A version retained from before a spill, then appended to long after the main line has grown
     *  through several trie levels. */
    @Test
    void branchingAfterSpillKeepsTheRetainedVersion() {
        PersistentVector<Integer> pv = PersistentVector.empty();
        for (int i = 0; i < 100; i++) {
            pv = pv.append(i);
        }
        PersistentVector<Integer> retained = pv;
        for (int i = 100; i < 100_000; i++) {
            pv = pv.append(i);
        }
        assertEquals(100, retained.size());
        assertEquals(100_000, pv.size());

        PersistentVector<Integer> branched = retained.append(-1);
        assertEquals(101, branched.size());
        assertEquals(-1, branched.get(100));
        assertEquals(100, retained.size());
        for (int i = 0; i < 100; i++) {
            assertEquals(i, retained.get(i));
            assertEquals(i, branched.get(i));
        }
        assertEquals(99_999, pv.get(99_999));
    }

    /**
     * The tail's claim is owned by one thread, so a non-owner has to copy instead of extending in
     * place. Eight threads start together off one shared vector and race for the same tail slot: at
     * most one may extend it, every other must copy, and all eight results plus the untouched base
     * must read correctly. Publication through the futures is safe, so a failure here is about
     * ownership, not about visibility.
     */
    @Test
    void concurrentAppendsOffOneVectorAllSucceed() throws Exception {
        int threads = 8;
        int each = 50;
        // A pool of its own, not the common pool: its parallelism is one less than the core count
        // and it is shared with everything else running, so on a small or busy machine the appends
        // would run in batches and the race this test is here to lose would not happen.
        ExecutorService pool = Executors.newFixedThreadPool(threads);
        try {
            for (int n : new int[] {0, 1, 5, 31, 32, 33, 1025}) {
                PersistentVector<Integer> shared = versions(n).get(n);
                CountDownLatch start = new CountDownLatch(1);
                List<Future<PersistentVector<Integer>>> futures = new ArrayList<>();
                for (int t = 0; t < threads; t++) {
                    int tag = -(t + 1);
                    futures.add(pool.submit(() -> {
                        start.await();
                        PersistentVector<Integer> mine = shared;
                        for (int k = 0; k < each; k++) {
                            mine = mine.append(tag);
                        }
                        return mine;
                    }));
                }
                start.countDown();

                for (int t = 0; t < threads; t++) {
                    PersistentVector<Integer> r = futures.get(t).get();
                    assertEquals(n + each, r.size(), "thread " + t + " size at n=" + n);
                    for (int i = 0; i < n; i++) {
                        assertEquals(i, r.get(i), "thread " + t + " prefix at n=" + n);
                    }
                    for (int i = n; i < n + each; i++) {
                        assertEquals(-(t + 1), r.get(i), "thread " + t + " own elements at n=" + n);
                    }
                }
                assertEquals(n, shared.size(), "the shared base changed at n=" + n);
            }
        } finally {
            pool.shutdownNow();
        }
    }

    @Test
    void equalsAndHashCodeMatchArrayListCrossType() {
        for (int n : new int[] {0, 1, 32, 33, 1025}) {
            List<Integer> oracle = new ArrayList<>();
            PersistentVector<Integer> pv = PersistentVector.empty();
            for (int i = 0; i < n; i++) {
                oracle.add(i);
                pv = pv.append(i);
            }
            assertEquals(oracle, pv);
            assertEquals(pv, oracle);
            assertEquals(oracle.hashCode(), pv.hashCode(), "hashCode at n=" + n);
        }
        PersistentVector<Integer> a = PersistentVector.from(List.of(1, 2, 3));
        assertNotEquals(a, List.of(1, 2, 4));
        assertNotEquals(a, List.of(1, 2));
    }

    @Test
    void isImmutable() {
        PersistentVector<Integer> pv = PersistentVector.from(List.of(1, 2, 3));
        assertThrows(UnsupportedOperationException.class, () -> pv.add(4));
        assertThrows(UnsupportedOperationException.class, () -> pv.set(0, 9));
        assertThrows(UnsupportedOperationException.class, () -> pv.remove(0));
    }

    @Test
    void aBuilderReadsAsTheListItIsBecoming() {
        // A builder rides the accumulator slot of a fold that only grows its list, where the
        // generated bytecode holds it as a java.util.List. What it has been given must read back
        // through the trie it has already spilled into as well as through the tail it is filling.
        for (int n : SIZES) {
            List<Integer> oracle = new ArrayList<>();
            PersistentVector.Builder<Integer> builder = new PersistentVector.Builder<>();
            for (int i = 0; i < n; i++) {
                oracle.add(i);
                builder.add(i);
            }
            assertEquals(n, builder.size(), "size at n=" + n);
            for (int i = 0; i < n; i++) {
                assertEquals(oracle.get(i), builder.get(i), "get(" + i + ") at n=" + n);
            }
            assertEquals(oracle, builder, "the builder as a list at n=" + n);
            assertEquals(oracle, builder.build(), "the vector it seals at n=" + n);
        }
    }

    @Test
    void iteratorExhaustionThrows() {
        PersistentVector<Integer> pv = PersistentVector.ofSingle(7);
        Iterator<Integer> it = pv.iterator();
        assertTrue(it.hasNext());
        assertEquals(7, it.next());
        assertFalse(it.hasNext());
        assertThrows(java.util.NoSuchElementException.class, it::next);
    }
}
