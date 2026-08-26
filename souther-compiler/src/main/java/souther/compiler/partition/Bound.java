package souther.compiler.partition;

/**
 * Where a region of a quantity's values stops on one side, and whether the place it stops at is one
 * of its own.
 *
 * <p><b>A place and not a level.</b> Where a region stops is where the rules part the values, and a
 * rule may part them at a place the quantity stands at no value of: {@code 3 * d <= 1} stops a region
 * at a third, and no decimal this language writes is a third. Held as a {@link Level}, the end would
 * have to be rounded to a number the region does not stop at, which is the reading
 * {@link CutPosition} exists to refuse — so this is where a region stops and never what it holds.
 *
 * <p>Which is why {@link #admitsFromBelow} and {@link #admitsFromAbove} take a level and compare it
 * through the position. A level is one of the quantity's own values and the place may be written in
 * a multiple of it; brought together as they stand, a region above a third kept every decimal up to
 * one.
 *
 * <p>Nothing here needs an order to compare with. {@link CutPosition#compare(Level)} settles it by
 * multiplying, and falls back to the places themselves on an order with no numbers — so a region on
 * a string is written the same way a region on a decimal is.
 *
 * @param at        where the region stops
 * @param inclusive whether the value at that place, where the quantity takes one, is in the region
 */
public record Bound(CutPosition at, boolean inclusive) {

    public Bound {
        if (at == null) {
            throw new IllegalArgumentException("a bound stops somewhere");
        }
    }

    /** A bound at one of the quantity's own values, which is what a region between two values has. */
    public static Bound at(Level level, boolean inclusive) {
        return new Bound(CutPosition.at(level), inclusive);
    }

    /** The same end with its place written the one way, for an identity to be built from
     *  ({@link CutPosition#canonical()}). */
    public Bound canonical() {
        return new Bound(at.canonical(), inclusive);
    }

    /** Whether {@code value} is on the upper side of this, read as the lower end of a region. */
    public boolean admitsFromBelow(Level value) {
        int order = at.compare(value);
        return order > 0 || (inclusive && order == 0);
    }

    /** The same read as the upper end. */
    public boolean admitsFromAbove(Level value) {
        int order = at.compare(value);
        return order < 0 || (inclusive && order == 0);
    }

    /**
     * The tighter of two lower ends, where a {@code null} is no end and so never the tighter.
     *
     * <p>At one place the two are the same end asked of two rules, and a region cannot hold what
     * either of them refuses — so the place survives only where both admit it. The same rule
     * {@link souther.compiler.numeric.Endpoint#lower} states, asked of a place rather than of a
     * count.
     */
    public static Bound lower(Bound a, Bound b) {
        if (a == null) {
            return b;
        }
        if (b == null) {
            return a;
        }
        int order = b.at.compareTo(a.at);
        if (order == 0) {
            return a.inclusive && !b.inclusive ? b : a;
        }
        return order > 0 ? b : a;
    }

    /** The tighter of two upper ends, the same way. */
    public static Bound upper(Bound a, Bound b) {
        if (a == null) {
            return b;
        }
        if (b == null) {
            return a;
        }
        int order = b.at.compareTo(a.at);
        if (order == 0) {
            return a.inclusive && !b.inclusive ? b : a;
        }
        return order < 0 ? b : a;
    }

    @Override
    public String toString() {
        return (inclusive ? "[" : "(") + at.key();
    }
}
