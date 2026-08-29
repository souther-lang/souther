package souther.compiler.partition;

import java.util.ArrayList;
import java.util.List;

/**
 * Which values of a quantity a coverage item stands for.
 *
 * <p>A finite union of runs, and the whole of what an item means. What a row has to do to be at an
 * item used to be written twice — once as a question about a value and once as the walk that looked
 * for one — and the two came apart wherever the item was a run: what was in it was decided exactly
 * and what was looked for was found by stepping, so a run the quantity fills had values in it that
 * nothing could name (issues #901, #903).
 *
 * <p><b>The set and never the order.</b> Whether a quantity takes any value in one of these runs is
 * the quantity's answer ({@link LevelSpace}), and which run to look in first is a searching policy.
 * Neither is here: a rule that singles a value out leaves the run under it and the run over it, and
 * nothing about the two says which one a reader should be offered.
 *
 * <p>A union rather than a run because one item is a union. A rule that names a value puts every
 * other value in one class, and that class is two runs — written as one, it needed an end nobody
 * wrote.
 *
 * @param parts the runs, none of which is written down with its ends crossed. An empty list is the
 *              item nothing stands at
 */
public record LevelRegion(List<LevelInterval> parts) {

    /** Every value the order has. */
    public static final LevelRegion EVERYTHING = of(LevelInterval.EVERYTHING);

    public LevelRegion {
        parts = List.copyOf(parts);
    }

    /** One run, or the item nothing stands at where its ends cross. */
    public static LevelRegion of(LevelInterval only) {
        return only == null || only.crossed()
                ? new LevelRegion(List.of()) : new LevelRegion(List.of(only));
    }

    /** The one level, and nothing else. */
    public static LevelRegion point(Level at) {
        return of(LevelInterval.point(at));
    }

    /** The same values with every end written the one way, for an identity to be built from. */
    public LevelRegion canonical() {
        return new LevelRegion(parts.stream().map(LevelInterval::canonical).toList());
    }

    /** Whether a value of the quantity stands at this item. */
    public boolean contains(Level value) {
        return parts.stream().anyMatch(part -> part.contains(value));
    }

    /**
     * The same item without one value of it.
     *
     * <p>Which is what a point away from a border asks for, and what a rule that singles a value out
     * leaves. Null takes nothing out, because an item whose line is at a place the quantity stands
     * at no value of has no value to leave out.
     */
    public LevelRegion without(Level value) {
        if (value == null) {
            return this;
        }
        List<LevelInterval> left = new ArrayList<>();
        for (LevelInterval part : parts) {
            left.addAll(part.without(value));
        }
        return new LevelRegion(left);
    }

    @Override
    public String toString() {
        return parts.isEmpty() ? "nothing"
                : String.join(" or ", parts.stream().map(LevelInterval::toString).toList());
    }
}
