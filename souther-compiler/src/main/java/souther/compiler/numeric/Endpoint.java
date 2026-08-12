package souther.compiler.numeric;

/**
 * Where a range stops, and whether the count it stops at is one of its own.
 *
 * <p>A count and not a value. A range is a range of the algebra's coordinates — days for a date,
 * seconds for a date-time, the number itself for an {@code Int} — and what a person writes at the
 * position is the carrier's to spell. Held as a bare number, an end was the one place a day count
 * could be handed to something expecting the number a model wrote.
 */
public record Endpoint(Place at, boolean inclusive) {

    public static Endpoint inclusive(Place at) {
        return new Endpoint(at, true);
    }

    public static Endpoint exclusive(Place at) {
        return new Endpoint(at, false);
    }

    /**
     * The tighter of two lower bounds, where a {@code null} is no bound and so never the tighter.
     *
     * <p>At one count the two are the same edge asked of two rules, and a conjunction cannot admit
     * what either conjunct refuses — so the count survives only where both admit it.
     */
    public static Endpoint lower(Endpoint a, Endpoint b) {
        if (a == null) {
            return b;
        }
        if (b == null) {
            return a;
        }
        int order = b.at().compareTo(a.at());
        if (order == 0) {
            return a.inclusive() && !b.inclusive() ? b : a;
        }
        return order > 0 ? b : a;
    }

    /** The tighter of two upper bounds, the same way. */
    public static Endpoint upper(Endpoint a, Endpoint b) {
        if (a == null) {
            return b;
        }
        if (b == null) {
            return a;
        }
        int order = b.at().compareTo(a.at());
        if (order == 0) {
            return a.inclusive() && !b.inclusive() ? b : a;
        }
        return order < 0 ? b : a;
    }

    /**
     * Whether anything at all lies between a lower bound and an upper one, either of which may be
     * {@code null} for no bound.
     *
     * <p>Not a comparison of the two counts. At one count they are equal whichever way they are
     * written, and what decides it is whether both admit that count — over a dense carrier there is
     * nothing else between them to fall back on. A discrete carrier never reaches here open: its
     * strict bounds are sharpened onto the adjacent count where they are recorded.
     */
    public static boolean someValueLiesBetween(Endpoint low, Endpoint high) {
        if (low == null || high == null) {
            return true;
        }
        int order = low.at().compareTo(high.at());
        if (order > 0) {
            return false;
        }
        return order < 0 || (low.inclusive() && high.inclusive());
    }

}
