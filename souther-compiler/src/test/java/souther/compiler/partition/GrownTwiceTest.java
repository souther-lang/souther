package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.ObservedValue;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The values a value becomes grown by one element and then by two come in the order a walk can be
 * seen to go past its first element on, and each is made when it is asked for.
 *
 * <p>The grower here makes a list one longer for each of {@code values} numbers, one at a time, and
 * counts how many it has made: what the search is given runs for follows the candidates it takes,
 * and a grower asked for its first must not have been asked for all.
 */
class GrownTwiceTest {

    private static ObservedValue whole(long n) {
        return new ObservedValue.Integer(n);
    }

    private static ObservedValue listOf(ObservedValue... elements) {
        return new ObservedValue.Sequence(List.of(elements));
    }

    private static int elementsIn(ObservedValue value) {
        return ((ObservedValue.Sequence) value).elements().size();
    }

    /** A list of the kind {@code which} names, made one element longer for each of the values. */
    private static final class Grower {

        private final int values;

        private int made;

        Grower(int values) {
            this.values = values;
        }

        Iterator<ObservedValue> grow(ObservedValue value, NearbyValues.Lists which) {
            ObservedValue.Sequence held = (ObservedValue.Sequence) value;
            if (!which.admits(held.elements().size())) {
                return Collections.emptyIterator();
            }
            return new Iterator<>() {

                private int next = 1;

                @Override
                public boolean hasNext() {
                    return next <= values;
                }

                @Override
                public ObservedValue next() {
                    if (!hasNext()) {
                        throw new NoSuchElementException();
                    }
                    made++;
                    List<ObservedValue> elements = new ArrayList<>(held.elements());
                    elements.add(whole(next++));
                    return new ObservedValue.Sequence(elements);
                }
            };
        }
    }

    /**
     * From a list holding nothing the first candidate is a list of two, and the growths made to
     * reach it are two: not every list of one that could be made, however many values there are.
     */
    @Test
    void aListHoldingNothingIsGrownToTwoBeforeAnythingElseIsMade() {
        Grower grower = new Grower(10_000);

        Iterator<ObservedValue> grown = GrownTwice.of(listOf(), grower::grow);
        ObservedValue first = grown.next();

        assertEquals(2, elementsIn(first));
        assertTrue(grower.made <= 2, () -> "made " + grower.made + " to hand over the first");
    }

    /** A list holding something is grown by one before it is grown by two. */
    @Test
    void aListHoldingSomethingIsGrownByOneFirst() {
        Grower grower = new Grower(3);

        Iterator<ObservedValue> grown = GrownTwice.of(listOf(whole(7)), grower::grow);

        assertEquals(listOf(whole(7), whole(1)), grown.next());
        assertEquals(listOf(whole(7), whole(2)), grown.next());
        assertEquals(listOf(whole(7), whole(3)), grown.next());
        assertEquals(3, elementsIn(grown.next()), "and then by two");
    }

    /** What no list of two is reached by is made last and is not left out. */
    @Test
    void whatNoListOfTwoIsReachedByIsMadeLastAndNotLeftOut() {
        List<ObservedValue> all = new ArrayList<>();
        GrownTwice.of(listOf(), new Grower(3)::grow).forEachRemaining(all::add);

        assertEquals(listOf(whole(1)), all.get(all.size() - 3), "grown once, after the pairs");
        assertTrue(all.contains(listOf(whole(1))));
        assertTrue(all.contains(listOf(whole(3))));
        assertTrue(all.contains(listOf(whole(2), whole(3))));
        assertEquals(2, elementsIn(all.getFirst()));
        assertEquals(all.size(), Set.copyOf(all).size(), "and none is made twice");
    }
}
