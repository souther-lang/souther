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

    /** A burst by another thread in one of two countings is not in the least of them. */
    @Test
    void theLeastOfTwoCountingsLeavesOutWhatAStrayThreadAddedToOne() {
        try (Visits visits = Visits.into(List.of(Values.class))) {
            assertTrue(visits.during(aBurstByAnotherThreadOnTheFirstRun()) >= 1000);
            assertEquals(0, visits.duringLeast(aBurstByAnotherThreadOnTheFirstRun()));
        }
    }

    /** Work that does nothing itself, and on its first run has another thread go into the values. */
    private static Runnable aBurstByAnotherThreadOnTheFirstRun() {
        Values.Leaf leaf = new Values.Leaf(1);
        AtomicBoolean first = new AtomicBoolean(true);
        return () -> {
            if (first.getAndSet(false)) {
                Workers.ended(Workers.started("stray-burst", () -> {
                    for (int at = 0; at < 1000; at++) {
                        leaf.value();
                    }
                }), Duration.ofMinutes(1), "the burst ended");
            }
        };
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
}
