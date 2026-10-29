package souther.compiler.partition;

import souther.compiler.observe.ObservedValue;

import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.function.BiFunction;
import java.util.function.Supplier;

/**
 * The values a value becomes grown by one element and then by two, the ones a walk can be seen to go
 * past its first element on first.
 *
 * <p>A walk over a list parts from a rewrite of it only from a second step on, so a list holding
 * nothing, grown by one element, is still a list no rewrite answers differently on, and a candidate
 * is worth a run before another when a list in it holds two. Which candidate that is, is not found
 * by looking through them and keeping the ones that do: it is the kind of list each growth is of.
 * Growing a list that holds something makes a list of two or more; growing one that holds nothing
 * and then growing the list it made does too. So the candidates are made in that order by growing
 * the lists of the kind that makes them, and nothing is looked through or set aside to find them —
 * the first candidate is the first one made, whatever the number of values there are to grow by.
 *
 * <p>The rest follow, so that what the search is given runs for is spent on them last and not
 * never: growing what holds nothing, and then the growths by two that no list of two was reached by.
 */
final class GrownTwice {

    private GrownTwice() {
    }

    /** The kinds of list grown, one growth after another, in the order the candidates are made. */
    private static final List<List<NearbyValues.Lists>> LADDER = List.of(
            // A list holding something, grown: two or more.
            List.of(NearbyValues.Lists.HOLDING_SOME),
            // A list holding nothing, grown, and then the list that made: two or more.
            List.of(NearbyValues.Lists.HOLDING_NONE, NearbyValues.Lists.HOLDING_SOME),
            // What no list of two was made by, grown once and then twice.
            List.of(NearbyValues.Lists.HOLDING_NONE),
            List.of(NearbyValues.Lists.HOLDING_SOME, NearbyValues.Lists.HOLDING_SOME),
            List.of(NearbyValues.Lists.HOLDING_SOME, NearbyValues.Lists.HOLDING_NONE),
            List.of(NearbyValues.Lists.HOLDING_NONE, NearbyValues.Lists.HOLDING_NONE));

    /**
     * The values {@code value} becomes grown by one element and then by two, in the lists
     * {@code grow} is told to grow.
     *
     * @param grow the values a value becomes with one list of the kind it is handed one element
     *             longer; handed over one at a time
     */
    static Iterator<ObservedValue> of(
            ObservedValue value,
            BiFunction<ObservedValue, NearbyValues.Lists, Iterator<ObservedValue>> grow) {
        List<Supplier<Iterator<ObservedValue>>> stages = LADDER.stream()
                .<Supplier<Iterator<ObservedValue>>>map(kinds -> () -> grownBy(value, kinds, grow))
                .toList();
        Iterator<ObservedValue> all = new Iterator<>() {

            private int stage;

            private Iterator<ObservedValue> current = Collections.emptyIterator();

            @Override
            public boolean hasNext() {
                while (!current.hasNext() && stage < stages.size()) {
                    current = stages.get(stage++).get();
                }
                return current.hasNext();
            }

            @Override
            public ObservedValue next() {
                if (!hasNext()) {
                    throw new NoSuchElementException();
                }
                return current.next();
            }
        };
        // A value two growths reach in either order, a list at a time in two lists, is made twice.
        // Held as it is handed over, which is as many as the search takes.
        return NearbyValues.filtered(all, new HashSet<ObservedValue>()::add);
    }

    /** {@code value} grown once for each kind in {@code kinds}, each growth of what the one before
     *  made. */
    private static Iterator<ObservedValue> grownBy(
            ObservedValue value, List<NearbyValues.Lists> kinds,
            BiFunction<ObservedValue, NearbyValues.Lists, Iterator<ObservedValue>> grow) {
        Iterator<ObservedValue> made = grow.apply(value, kinds.getFirst());
        for (NearbyValues.Lists kind : kinds.subList(1, kinds.size())) {
            made = NearbyValues.flat(made, each -> grow.apply(each, kind));
        }
        return made;
    }
}
