package souther.runtime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Random;
import org.junit.jupiter.api.Test;

/** {@link PersistentHashMap} against a {@link HashMap} oracle, including forced hash collisions. */
class PersistentHashMapTest {

    /** A key whose hashCode we control, to force CHAMP collision paths (equal hash, distinct value). */
    private record Key(int id, int hash) {
        @Override
        public int hashCode() {
            return hash;
        }
    }

    @Test
    void putGetRemoveMatchOracleRandomized() {
        Random rnd = new Random(42);
        for (int trial = 0; trial < 40; trial++) {
            Map<Integer, Integer> oracle = new HashMap<>();
            PersistentHashMap<Integer, Integer> phm = PersistentHashMap.empty();
            for (int op = 0; op < 400; op++) {
                int key = rnd.nextInt(80);
                if (rnd.nextInt(3) == 0 && !oracle.isEmpty()) {
                    oracle.remove(key);
                    phm = phm.without(key);
                } else {
                    int val = rnd.nextInt(1000);
                    oracle.put(key, val);
                    phm = phm.assoc(key, val);
                }
                assertEquals(oracle.size(), phm.size(), "size trial=" + trial + " op=" + op);
            }
            for (int k = 0; k < 80; k++) {
                assertEquals(oracle.get(k), phm.get(k), "get(" + k + ")");
                assertEquals(oracle.containsKey(k), phm.containsKey(k));
            }
            assertEquals(oracle, phm);
            assertEquals(phm, oracle);
            assertEquals(oracle.hashCode(), phm.hashCode());
        }
    }

    @Test
    void forcedCollisionsBehaveLikeOracle() {
        Map<Key, Integer> oracle = new HashMap<>();
        PersistentHashMap<Key, Integer> phm = PersistentHashMap.empty();
        // Many keys sharing a handful of hash buckets -> exercises HashCollisionNode + deep tries.
        for (int i = 0; i < 200; i++) {
            Key k = new Key(i, i % 4);   // only 4 distinct hashes for 200 keys
            oracle.put(k, i);
            phm = phm.assoc(k, i);
        }
        assertEquals(oracle.size(), phm.size());
        for (Map.Entry<Key, Integer> e : oracle.entrySet()) {
            assertEquals(e.getValue(), phm.get(e.getKey()));
        }
        assertEquals(oracle, phm);
        // remove half, in a shuffled order
        java.util.List<Key> keys = new java.util.ArrayList<>(oracle.keySet());
        java.util.Collections.shuffle(keys, new Random(7));
        for (int i = 0; i < keys.size(); i += 2) {
            oracle.remove(keys.get(i));
            phm = phm.without(keys.get(i));
        }
        assertEquals(oracle.size(), phm.size());
        assertEquals(oracle, phm);
        for (Key k : keys) {
            assertEquals(oracle.get(k), phm.get(k));
        }
    }

    @Test
    void allKeysSameHash() {
        PersistentHashMap<Key, Integer> phm = PersistentHashMap.empty();
        Map<Key, Integer> oracle = new HashMap<>();
        for (int i = 0; i < 50; i++) {
            Key k = new Key(i, 999);   // every key collides fully
            phm = phm.assoc(k, i);
            oracle.put(k, i);
        }
        assertEquals(50, phm.size());
        assertEquals(oracle, phm);
        phm = phm.without(new Key(10, 999));
        oracle.remove(new Key(10, 999));
        assertEquals(49, phm.size());
        assertNull(phm.get(new Key(10, 999)));
        assertEquals(oracle, phm);
    }

    @Test
    void replaceKeepsSizeNoOpEqualValueSharesInstance() {
        PersistentHashMap<String, Integer> a = PersistentHashMap.<String, Integer>empty()
                .assoc("x", 1).assoc("y", 2);
        PersistentHashMap<String, Integer> b = a.assoc("x", 1);   // equal value -> unchanged
        assertTrue(a == b, "assoc of an equal value must return the same instance");
        PersistentHashMap<String, Integer> c = a.assoc("x", 9);   // replace
        assertEquals(2, c.size());
        assertEquals(9, c.get("x"));
        assertEquals(1, a.get("x"), "original is untouched");
    }

    @Test
    void removeAbsentReturnsSameInstance() {
        PersistentHashMap<String, Integer> a = PersistentHashMap.<String, Integer>empty().assoc("x", 1);
        assertTrue(a == a.without("nope"));
    }

    @Test
    void fromAndIterationOrderDeterministic() {
        Map<String, Integer> src = new LinkedHashMap<>();
        src.put("a", 1);
        src.put("b", 2);
        src.put("c", 3);
        PersistentHashMap<String, Integer> one = PersistentHashMap.from(src);
        PersistentHashMap<String, Integer> two = PersistentHashMap.from(src);
        assertEquals(one.keySet().toString(), two.keySet().toString(),
                "iteration order must be deterministic for the same keys");
        assertEquals(src, one);
        assertTrue(PersistentHashMap.from(one) == one, "from must share a PersistentHashMap");
    }

    @Test
    void isImmutable() {
        PersistentHashMap<String, Integer> a = PersistentHashMap.<String, Integer>empty().assoc("x", 1);
        assertThrows(UnsupportedOperationException.class, () -> a.put("y", 2));
        assertThrows(UnsupportedOperationException.class, () -> a.remove("x"));
        assertThrows(UnsupportedOperationException.class, a::clear);
    }

    @Test
    void emptyMapQueries() {
        PersistentHashMap<String, Integer> e = PersistentHashMap.empty();
        assertEquals(0, e.size());
        assertTrue(e.isEmpty());
        assertNull(e.get("x"));
        assertFalse(e.containsKey("x"));
        assertFalse(e.entrySet().iterator().hasNext());
    }

    /**
     * The bulk builder fills its nodes in place, so what it produces has to be indistinguishable
     * from the same entries added one at a time — same contents, same size, and the same iteration
     * order. The order is asserted because two ways of building one map must give one trie, not
     * because anything downstream may read it: the boundary settles its own order (see
     * {@link Representations}), and the language specifies none.
     */
    @Test
    void builderProducesTheSameMapAsRepeatedAssoc() {
        Random rnd = new Random(7);
        for (int n : new int[] {0, 1, 2, 31, 32, 33, 1023, 1024, 1025, 10_000}) {
            Map<Integer, Integer> oracle = new LinkedHashMap<>();
            for (int i = 0; i < n; i++) {
                oracle.put(rnd.nextInt(n * 2 + 1), i);   // duplicate keys, so later entries overwrite
            }
            PersistentHashMap<Integer, Integer> viaAssoc = PersistentHashMap.empty();
            for (Map.Entry<Integer, Integer> e : oracle.entrySet()) {
                viaAssoc = viaAssoc.assoc(e.getKey(), e.getValue());
            }
            PersistentHashMap<Integer, Integer> viaBuilder = PersistentHashMap.from(oracle);

            assertEquals(oracle.size(), viaBuilder.size(), "size at n=" + n);
            assertEquals(viaAssoc, viaBuilder, "contents at n=" + n);
            assertEquals(oracle, viaBuilder, "oracle at n=" + n);
            assertEquals(viaAssoc.keySet().stream().toList(), viaBuilder.keySet().stream().toList(),
                    "iteration order at n=" + n);
        }
    }

    /** Hash collisions take the builder down the {@code HashCollisionNode} path, which it does not
     *  own; it has to keep building correctly there too. */
    @Test
    void builderHandlesCollisionsLikeRepeatedAssoc() {
        Map<Key, Integer> oracle = new LinkedHashMap<>();
        for (int i = 0; i < 200; i++) {
            oracle.put(new Key(i, i % 5), i);   // 5 distinct hashes, 40 keys each
        }
        PersistentHashMap<Key, Integer> viaAssoc = PersistentHashMap.empty();
        for (Map.Entry<Key, Integer> e : oracle.entrySet()) {
            viaAssoc = viaAssoc.assoc(e.getKey(), e.getValue());
        }
        PersistentHashMap<Key, Integer> viaBuilder = PersistentHashMap.from(oracle);
        assertEquals(200, viaBuilder.size());
        assertEquals(viaAssoc, viaBuilder);
        assertEquals(viaAssoc.keySet().stream().toList(), viaBuilder.keySet().stream().toList());
    }

    /**
     * Once built, the map is an ordinary persistent one: the builder's trie must not stay writable.
     * If a later {@code assoc} could still write a node in place, the map it was derived from would
     * change under it — this is the test that fails if ownership ever leaks past {@code build}.
     */
    @Test
    void aBuiltMapIsPersistentAfterwards() {
        Map<Integer, Integer> seed = new LinkedHashMap<>();
        for (int i = 0; i < 500; i++) {
            seed.put(i, i);
        }
        PersistentHashMap<Integer, Integer> built = PersistentHashMap.from(seed);

        PersistentHashMap<Integer, Integer> plusOne = built.assoc(1000, 1000);
        PersistentHashMap<Integer, Integer> overwritten = built.assoc(7, -7);
        PersistentHashMap<Integer, Integer> removed = built.without(3);

        assertEquals(500, built.size(), "the built map changed");
        assertEquals(7, built.get(7));
        assertEquals(3, built.get(3));
        assertNull(built.get(1000));

        assertEquals(501, plusOne.size());
        assertEquals(-7, overwritten.get(7));
        assertEquals(7, plusOne.get(7));
        assertEquals(499, removed.size());
        assertNull(removed.get(3));
        for (int i = 0; i < 500; i++) {
            assertEquals(i, built.get(i), "built lost " + i);
        }
    }

    /**
     * The builder against a {@link LinkedHashMap} oracle, driven the way a fold drives it: a read of a
     * key followed by a write of one, sometimes the same key and sometimes another. Reading is what
     * lets the next write skip the descent (the probe), so what this holds is that the write lands
     * where the oracle says whatever came between them.
     */
    @Test
    void aBuilderReadAndThenWrittenAgreesWithAnOracle() {
        Map<Integer, Integer> oracle = new LinkedHashMap<>();
        PersistentHashMap.Builder<Integer, Integer> builder = new PersistentHashMap.Builder<>();
        int seed = 12345;
        for (int step = 0; step < 20_000; step++) {
            seed = seed * 1103515245 + 12345;
            int read = Math.floorMod(seed >> 8, 400);
            int written = Math.floorMod(seed >> 16, 400);
            // The read the builder answers must be the oracle's, and the write that follows it must
            // land whether or not it is the key just read.
            assertEquals(oracle.get(read), builder.get(read), "read of " + read + " at step " + step);
            int value = step;
            oracle.put(written, value);
            builder.set(written, value);
            assertEquals(oracle.size(), builder.size(), "size at step " + step);
        }
        assertEquals(oracle, builder);
        assertEquals(oracle, builder.build());
    }

    /** A read that finds nothing leaves nothing behind: the write that follows adds the key rather
     *  than overwriting whatever the last successful read pointed at. */
    @Test
    void aWriteAfterAReadThatMissedAdds() {
        PersistentHashMap.Builder<Integer, Integer> builder = new PersistentHashMap.Builder<>();
        builder.set(1, 10);
        assertEquals(10, builder.get(1));
        assertNull(builder.get(2));
        builder.set(2, 20);
        assertEquals(10, builder.get(1));
        assertEquals(20, builder.get(2));
        assertEquals(2, builder.size());
    }

    /** A builder is single-use, for the reason the vector's is: the map it built shares the nodes it
     *  filled. */
    @Test
    void aBuilderRefusesToWriteAfterItHasBuilt() {
        PersistentHashMap.Builder<Integer, Integer> builder = new PersistentHashMap.Builder<>();
        builder.set(1, 10);
        PersistentHashMap<Integer, Integer> built = builder.build();
        assertThrows(IllegalStateException.class, () -> builder.set(2, 20));
        assertEquals(Map.of(1, 10), built);
    }
}
