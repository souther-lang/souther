package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;

import java.util.List;

/**
 * A place on a position's order where its behavior is expected to change.
 *
 * <p>The cuts of one position are merged into one exclusive, exhaustive partition — {@code x < 0} and
 * {@code x < 10} written separately are three intervals and not two overlapping pairs — while
 * {@link #origins} keeps every rule that put a cut here. That is the asymmetry: what the classes are
 * is a property of the position, and what has to be exercised at a boundary is a property of each
 * rule that drew it.
 *
 * <p>Held as the count and the carrier it is on, rather than as the value. A cut comes from a range,
 * and a range is a range of counts; writing it out as a value at the moment it is recorded meant
 * every reader afterwards had to work out which of the two it was holding, and one of them read a
 * day count as the number a model wrote.
 */
public record Cut(Carrier carrier, Count at, List<OriginRef> origins) {

    public Cut {
        origins = List.copyOf(origins);
    }

    public static Cut at(Carrier carrier, Count at, OriginRef origin) {
        return new Cut(carrier, at, List.of(origin));
    }

    /** The same cut, also drawn by {@code origin}. */
    public Cut and(OriginRef origin) {
        List<OriginRef> all = new java.util.ArrayList<>(origins);
        all.add(origin);
        return new Cut(carrier, at, all);
    }

    /** Where this line is drawn, as a value rather than as the count it is recorded at. */
    public ObservedValue value() {
        return carrier.valueOf(at);
    }

    /** What makes two cuts one cut: the place on the order, and not how the number was written.
     * {@code invariant value >= 0.00} and {@code guard x <= 0m} draw one line; keyed by spelling they
     * are two, and then a position has two classes both holding zero. */
    public String key() {
        return at.key();
    }
}
