package souther.compiler.collect;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What is kept for a key is what was made of it, and is made again only when the key is no longer
 * in its set. Keys that hash alike share a set, which is the case a direct-mapped table loses.
 */
class AValueKeptForAKeyIsMadeOnceWhileItsSetHoldsItTest {

    /** A key whose hash is chosen, so that two keys can be made to fall in one set. */
    private record Key(int name, int hash) {
        @Override
        public int hashCode() {
            return hash;
        }
    }

    private final AtomicInteger made = new AtomicInteger();

    private String make(Key key) {
        made.incrementAndGet();
        return "value of " + key.name();
    }

    @Test
    void anEqualKeyAskedAgainIsNotMadeAgain() {
        HeldByKey<Key, String> table = new HeldByKey<>(4);
        assertEquals("value of 1", table.get(new Key(1, 7), this::make));
        assertEquals("value of 1", table.get(new Key(1, 7), this::make));
        assertEquals(1, made.get());
    }

    @Test
    void twoKeysOfOneHashAskedInTurnAreMadeOnceEach() {
        HeldByKey<Key, String> table = new HeldByKey<>(4);
        Key a = new Key(1, 7);
        Key b = new Key(2, 7);
        for (int i = 0; i < 100; i++) {
            assertEquals("value of 1", table.get(a, this::make));
            assertEquals("value of 2", table.get(b, this::make));
        }
        assertEquals(2, made.get());
    }

    @Test
    void threeKeysOfOneHashAreEachGivenTheirOwnValueWhateverIsKept() {
        HeldByKey<Key, String> table = new HeldByKey<>(4);
        for (int round = 0; round < 20; round++) {
            for (int name = 1; name <= 3; name++) {
                assertEquals("value of " + name, table.get(new Key(name, 7), this::make));
            }
        }
    }

    @Test
    void manyMoreKeysThanSlotsAreEachGivenTheirOwnValue() {
        HeldByKey<Key, String> table = new HeldByKey<>(3);
        for (int round = 0; round < 3; round++) {
            for (int name = 0; name < 1_000; name++) {
                assertEquals("value of " + name, table.get(new Key(name, name * 31), this::make));
            }
        }
    }

    @Test
    void threadsAskingTogetherAreEachGivenTheValueOfTheirKey() throws Exception {
        HeldByKey<Key, String> table = new HeldByKey<>(3);
        try (ExecutorService pool = Executors.newFixedThreadPool(4)) {
            List<Future<Integer>> runs = new ArrayList<>();
            for (int thread = 0; thread < 4; thread++) {
                int seed = thread;
                runs.add(pool.submit(() -> {
                    int wrong = 0;
                    for (int i = 0; i < 20_000; i++) {
                        int name = (i * 7 + seed) % 40;
                        if (!("value of " + name).equals(table.get(new Key(name, name % 5), this::make))) {
                            wrong++;
                        }
                    }
                    return wrong;
                }));
            }
            for (Future<Integer> run : runs) {
                assertEquals(0, run.get());
            }
        }
    }
}
