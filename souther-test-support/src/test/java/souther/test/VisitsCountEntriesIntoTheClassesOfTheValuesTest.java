package souther.test;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a walk allocates is nothing for a walk that only descends, so a walk over values is told by
 * how many times it went into them: once per descent whatever the walk allocates, and nothing for
 * work that did not reach them.
 */
class VisitsCountEntriesIntoTheClassesOfTheValuesTest {

    private static final int LENGTH = 10;

    private static Values.Node sharedChain(int length) {
        Values.Node held = new Values.Leaf(1);
        for (int at = 0; at < length; at++) {
            held = new Values.Branch(held, held);
        }
        return held;
    }

    private static long everyWay(Values.Node node) {
        return node instanceof Values.Branch branch
                ? everyWay(branch.left()) + everyWay(branch.right()) : 1;
    }

    private static long eachOnce(Values.Node node, Set<Values.Node> seen) {
        if (!seen.add(node)) {
            return 0;
        }
        return node instanceof Values.Branch branch
                ? eachOnce(branch.left(), seen) + eachOnce(branch.right(), seen) : 1;
    }

    @Test
    void aWalkThatDescendsWithoutAllocatingIsCountedOncePerDescent() {
        Values.Node chain = sharedChain(LENGTH);
        try (Visits visits = Visits.into(List.of(Values.class))) {
            Visits.Counted<Long> walked = visits.count(() -> everyWay(chain));
            assertEquals(1L << LENGTH, walked.value());
            assertEquals(2L * ((1L << LENGTH) - 1), walked.visits(),
                    "left() and right() of each branch on every way down");
        }
    }

    @Test
    void aWalkThatKeepsWhatItSawVisitsEachPartOnce() {
        Values.Node chain = sharedChain(LENGTH);
        try (Visits visits = Visits.into(List.of(Values.class))) {
            Visits.Counted<Long> walked = visits.count(() -> eachOnce(chain,
                    Collections.newSetFromMap(new IdentityHashMap<>())));
            assertEquals(2L * LENGTH, walked.visits());
        }
    }

    /** The counts are the JVM's, not the thread's, so a counter opened while another thread is
     *  running the counted classes is refused by its own calibration. */
    @Test
    void aCounterOpenedWhileAnotherThreadRunsTheCountedClassesIsRefused() throws InterruptedException {
        Values.Leaf leaf = new Values.Leaf(1);
        AtomicBoolean stop = new AtomicBoolean();
        CountDownLatch running = new CountDownLatch(1);
        Thread stray = Workers.started("stray-reader", () -> {
            while (!stop.get()) {
                leaf.value();
                running.countDown();
            }
        });
        try {
            running.await();
            assertThrows(AssertionError.class, () -> Visits.into(List.of(Values.class)));
        } finally {
            stop.set(true);
            Workers.ended(stray, Duration.ofMinutes(1), "the stray reader stopped");
        }
    }

    /**
     * Work that keeps what it did is counted at its first run, and a run after it is another and
     * cheaper work: so a count is taken once, on an input made for it, and the least of two runs of
     * one input is not the cost of the walk.
     */
    @Test
    void workThatKeepsWhatItDidCostsItsWalkOnlyTheFirstTime() {
        Values.Remembering remembering = new Values.Remembering(sharedChain(LENGTH));
        try (Visits visits = Visits.into(List.of(Values.class))) {
            long first = visits.during(remembering::settle);
            long again = visits.during(remembering::settle);
            assertTrue(first >= 1L << LENGTH, "the first run is the walk: " + first);
            assertTrue(again < first / 100, "the next is what was kept: " + again);
        }
    }

    @Test
    void workThatDoesNotReachTheValuesCountsNothingAndIsNotRefused() {
        try (Visits visits = Visits.into(List.of(Values.class))) {
            assertEquals(0, visits.count(() -> 1).visits());
        }
    }
}

/** The values walked, in a class of their own so that the walks are not among what is counted. */
final class Values {

    private Values() {}

    sealed interface Node permits Branch, Leaf {}

    record Branch(Node left, Node right) implements Node {}

    record Leaf(int value) implements Node {}

    /** Walks every way down once and keeps the answer. */
    static final class Remembering {
        private final Node chain;
        private Long settled;

        Remembering(Node chain) {
            this.chain = chain;
        }

        void settle() {
            if (settled == null) {
                settled = everyWay(chain);
            }
        }

        private static long everyWay(Node node) {
            return node instanceof Branch branch ? everyWay(branch.left()) + everyWay(branch.right()) : 1;
        }
    }
}
