package souther.compiler.collect;

import org.junit.jupiter.api.Test;
import souther.test.Allocated;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What is kept for a pair is what was made of the two, is made again only when the pair is no
 * longer in its set or was not to be kept, and is found without making anything. The order of a pair
 * is part of it, and pairs that hash alike share a set.
 */
class AValueKeptForAPairIsMadeOnceWhileItsSetHoldsItTest {

    /** An operand whose hash is chosen, so that two pairs can be made to fall in one set. */
    private record Operand(int name, int hash) {
        @Override
        public int hashCode() {
            return hash;
        }
    }

    private final AtomicInteger made = new AtomicInteger();

    private String make(Operand first, Operand second) {
        made.incrementAndGet();
        return first.name() + " with " + second.name();
    }

    private static boolean always(String value) {
        return true;
    }

    @Test
    void anEqualPairAskedAgainIsNotMadeAgain() {
        HeldByPair<Operand, Operand, String> table = new HeldByPair<>(4);
        assertEquals("1 with 2", table.get(new Operand(1, 7), new Operand(2, 3), this::make, v -> true));
        assertEquals("1 with 2", table.get(new Operand(1, 7), new Operand(2, 3), this::make, v -> true));
        assertEquals(1, made.get());
    }

    @Test
    void aPairTheOtherWayRoundIsAnotherPair() {
        HeldByPair<Operand, Operand, String> table = new HeldByPair<>(4);
        Operand a = new Operand(1, 7);
        Operand b = new Operand(2, 7);
        for (int i = 0; i < 100; i++) {
            assertEquals("1 with 2", table.get(a, b, this::make, v -> true));
            assertEquals("2 with 1", table.get(b, a, this::make, v -> true));
        }
        assertEquals(2, made.get(), "two pairs of one hash asked in turn are made once each");
    }

    @Test
    void aValueNotToBeKeptIsMadeAtEveryAsk() {
        HeldByPair<Operand, Operand, String> table = new HeldByPair<>(4);
        Operand a = new Operand(1, 7);
        Operand b = new Operand(2, 3);
        for (int i = 0; i < 10; i++) {
            assertEquals("1 with 2", table.get(a, b, this::make, v -> false));
        }
        assertEquals(10, made.get());
    }

    @Test
    void aValueNotToBeKeptLeavesWhatTheSetHolds() {
        HeldByPair<Operand, Operand, String> table = new HeldByPair<>(4);
        Operand a = new Operand(1, 7);
        Operand b = new Operand(2, 7);
        Operand c = new Operand(3, 7);
        table.get(a, a, this::make, v -> true);
        table.get(b, b, this::make, v -> true);
        table.get(c, c, this::make, v -> false);
        made.set(0);
        table.get(a, a, this::make, v -> true);
        table.get(b, b, this::make, v -> true);
        assertEquals(0, made.get());
    }

    @Test
    void manyMoreSetsOfPairsThanSlotsAreEachGivenTheirOwnValue() {
        HeldByPair<Operand, Operand, String> table = new HeldByPair<>(3);
        for (int round = 0; round < 3; round++) {
            for (int name = 0; name < 300; name++) {
                Operand first = new Operand(name, name % 11);
                Operand second = new Operand(name + 1, name % 5);
                assertEquals(name + " with " + (name + 1), table.get(first, second, this::make, v -> true));
            }
        }
    }

    /** What is found is handed out as it was kept, and finding it makes nothing — no pair either. */
    @Test
    void aPairFoundAllocatesNothing() {
        HeldByPair<Operand, Operand, String> table = new HeldByPair<>(4);
        Operand a = new Operand(1, 7);
        Operand b = new Operand(2, 7);
        String kept = table.get(a, b, this::make, AValueKeptForAPairIsMadeOnceWhileItsSetHoldsItTest::always);
        Operand[] firsts = new Operand[ASKS];
        Operand[] seconds = new Operand[ASKS];
        for (int i = 0; i < ASKS; i++) {
            firsts[i] = new Operand(1, 7);
            seconds[i] = new Operand(2, 7);
        }
        Runnable asking = () -> {
            for (int i = 0; i < ASKS; i++) {
                assertSame(kept, table.get(firsts[i], seconds[i],
                        AValueKeptForAPairIsMadeOnceWhileItsSetHoldsItTest::unmade,
                        AValueKeptForAPairIsMadeOnceWhileItsSetHoldsItTest::always));
            }
        };
        asking.run();
        long allocated = Allocated.byWhichMayBeNothing(asking);
        assertTrue(allocated < ASKS, "a pair found allocates nothing per ask, and " + allocated
                + " bytes were allocated for " + ASKS + " asks");
    }

    private static final int ASKS = 2_000;

    private static String unmade(Operand first, Operand second) {
        throw new AssertionError("made " + first + " with " + second + ", which was kept");
    }

    @Test
    void threadsAskingTogetherAreEachGivenTheValueOfTheirPair() throws Exception {
        HeldByPair<Operand, Operand, String> table = new HeldByPair<>(3);
        try (ExecutorService pool = Executors.newFixedThreadPool(4)) {
            List<Future<Integer>> runs = new ArrayList<>();
            for (int thread = 0; thread < 4; thread++) {
                int seed = thread;
                runs.add(pool.submit(() -> {
                    int wrong = 0;
                    for (int i = 0; i < 20_000; i++) {
                        int name = (i * 7 + seed) % 40;
                        Operand first = new Operand(name, name % 5);
                        Operand second = new Operand(name % 3, 1);
                        if (!(name + " with " + name % 3).equals(table.get(first, second, this::make, v -> true))) {
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
