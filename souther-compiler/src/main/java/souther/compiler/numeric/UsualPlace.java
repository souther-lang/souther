package souther.compiler.numeric;

/**
 * Where a number with no rule fixing it is looked for first, and the ends its order has of its own.
 *
 * <p>The ends are what tell a range a rule drew from one it was left: a range whose end is the
 * order's own was bounded by nobody on that side, and is entered nearest {@link #at}; a range a rule
 * closed on both sides is entered where every range is, from its end.
 *
 * @param at       the place itself, as the day today is of a date
 * @param least    the least value the order has
 * @param greatest the greatest value the order has
 */
public record UsualPlace(Place at, Place least, Place greatest) {

    public UsualPlace {
        if (at == null || least == null || greatest == null) {
            throw new IllegalArgumentException("a usual place is a place between two ends");
        }
    }

    /** Whether {@code within} reaches the order's own end on at least one side. */
    public boolean isOpenIn(NumericDomain.Bounds within) {
        Endpoint low = within == null ? null : within.min();
        Endpoint high = within == null ? null : within.max();
        return low == null || low.at().compareTo(least) <= 0
                || high == null || high.at().compareTo(greatest) >= 0;
    }
}
