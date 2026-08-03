package souther.compiler.partition;

import souther.compiler.observe.ObservedValue;

import java.util.List;

/**
 * A value where an input position's behavior is expected to change.
 *
 * <p>The cuts of one position are merged into one exclusive, exhaustive partition — {@code x < 0} and
 * {@code x < 10} written separately are three intervals and not two overlapping pairs — while
 * {@link #origins} keeps every rule that put a cut here. That is the asymmetry: what the classes are
 * is a property of the position, and what has to be exercised at a boundary is a property of each
 * rule that drew it.
 */
public record Cut(ObservedValue value, List<OriginRef> origins) {

    public Cut {
        origins = List.copyOf(origins);
    }

    public static Cut at(ObservedValue value, OriginRef origin) {
        return new Cut(value, List.of(origin));
    }

    /** The same cut, also drawn by {@code origin}. */
    public Cut and(OriginRef origin) {
        List<OriginRef> all = new java.util.ArrayList<>(origins);
        all.add(origin);
        return new Cut(value, all);
    }
}
