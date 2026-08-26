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
     * Whether this is the same end as {@code other}: the same place, admitted or refused the same
     * way.
     *
     * <p>{@link Place#sameAs}'s question asked of an end rather than of a place, and here for the
     * same reason it is there. A record derives {@code equals} from what it holds, which reaches
     * {@link java.math.BigDecimal#equals} and tells {@code 3.0} from {@code 3.00} — two spellings of
     * one place, which is what {@link Place#key} exists to say are one. An end is where a range
     * stops, and where it stops does not depend on how the rule that put it there wrote the number.
     *
     * <p>Both halves and not the place alone. At one place an inclusive end and an exclusive one
     * leave different values, and a conjunction of the two leaves the second — so a reader that
     * compared the places would call two ends one and take the wrong one's word for where the range
     * stops.
     *
     * <p>A {@code null} is no end, and no end is not the same end as one that is there.
     */
    public boolean sameAs(Endpoint other) {
        return other != null && inclusive == other.inclusive && at.sameAs(other.at);
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
