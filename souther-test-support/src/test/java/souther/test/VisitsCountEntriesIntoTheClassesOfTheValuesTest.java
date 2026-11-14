package souther.test;

import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

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
