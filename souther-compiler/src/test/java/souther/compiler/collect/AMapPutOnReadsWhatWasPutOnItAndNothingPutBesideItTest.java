package souther.compiler.collect;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What one of these reads under a key is what was put under it last on the way to it, whatever was
 * put on the maps it was made from afterwards or on the maps made beside it — keys of equal hashes,
 * of hashes alike in their low bits and of hashes alike in their high bits among them.
 */
class AMapPutOnReadsWhatWasPutOnItAndNothingPutBesideItTest {

    /** A key hashed as it is told to be, and equal by both. */
    private record Key(int hash, int id) {

        @Override
        public int hashCode() {
            return hash;
        }
    }

    /** Hashes that meet at every level of the trie: equal, alike below and alike above. */
    private static final int[] HASHES = {0, 1, 32, 1 << 16, (1 << 16) | 1, 1 << 30, -1,
            Integer.MIN_VALUE, Integer.MIN_VALUE | 1, 0x7fff_0000};

    private static final List<Key> KEYS = keys();

    private static List<Key> keys() {
        List<Key> out = new ArrayList<>();
        for (int hash : HASHES) {
            for (int id = 0; id < 3; id++) {
                out.add(new Key(hash, id));
            }
        }
        return out;
    }

    private static void assertReads(Map<Key, Integer> expected, SharingMap<Key, Integer> map) {
        for (Key each : KEYS) {
            assertEquals(expected.get(each), map.get(each), each.toString());
        }
    }

    @Test
    void everyMapMadeReadsWhatWasPutOnTheWayToItAndNoMore() {
        Random random = new Random(3024);
        List<SharingMap<Key, Integer>> made = new ArrayList<>();
        List<Map<Key, Integer>> expected = new ArrayList<>();
        made.add(SharingMap.empty());
        expected.add(Map.of());
        for (int step = 0; step < 4000; step++) {
            int from = random.nextInt(made.size());
            Key key = KEYS.get(random.nextInt(KEYS.size()));
            Map<Key, Integer> put = new HashMap<>(expected.get(from));
            put.put(key, step);
            made.add(made.get(from).with(key, step));
            expected.add(put);
        }
        for (int at = 0; at < made.size(); at++) {
            assertReads(expected.get(at), made.get(at));
        }
    }

    @Test
    void aKeyPutAgainReadsTheLaterValueAndTheMapBeforeTheEarlier() {
        Key key = new Key(7, 0);
        SharingMap<Key, Integer> once = SharingMap.<Key, Integer>empty().with(key, 1);
        SharingMap<Key, Integer> twice = once.with(key, 2);
        assertEquals(1, once.get(key));
        assertEquals(2, twice.get(key));
        assertNull(SharingMap.<Key, Integer>empty().get(key));
    }

    @Test
    void nothingIsNotAValueThatCanBePut() {
        assertThrows(NullPointerException.class,
                () -> SharingMap.<Key, Integer>empty().with(new Key(0, 0), null));
    }
}
