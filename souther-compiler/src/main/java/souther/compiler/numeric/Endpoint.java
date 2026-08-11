package souther.compiler.numeric;

/**
 * Where a range stops, and whether the count it stops at is one of its own.
 *
 * <p>A count and not a value. A range is a range of the algebra's coordinates — days for a date,
 * seconds for a date-time, the number itself for an {@code Int} — and what a person writes at the
 * position is the carrier's to spell. Held as a bare number, an end was the one place a day count
 * could be handed to something expecting the number a model wrote.
 */
public record Endpoint(Count at, boolean inclusive) {

    public static Endpoint inclusive(Count at) {
        return new Endpoint(at, true);
    }

    public static Endpoint exclusive(Count at) {
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

    /**
     * A count between a lower bound and an upper one, or {@code null} where they hold none.
     *
     * <p>The one way a pair of ends gives up a count, so that nothing deciding what to write reads an
     * end's count and loses whether the range holds it. An end the range holds is the count taken: it
     * is inside whatever other end there is, and it is the count a boundary wants written anyway. An
     * end the range stops short of is not one, and over a dense order there is no count beside it to
     * take instead — so the count comes from inside, between the ends where both are known and a step
     * in from the only one where there is one. Nothing about that step is the nearest count the range
     * holds; over a dense order there is no such thing. It is a count the range holds, chosen the same
     * way every time.
     *
     * <p>Over a discrete carrier each end moves onto the nearest whole count inside it first, which is
     * where a strict bound and a fractional one both become a count the carrier has.
     */
    public static Count valueBetween(Endpoint low, Endpoint high, Granularity spacing) {
        if (spacing == Granularity.DISCRETE) {
            Endpoint lo = whole(low, true);
            Endpoint hi = whole(high, false);
            if (!someValueLiesBetween(lo, hi)) {
                return null;
            }
            return lo != null ? lo.at() : hi != null ? hi.at() : Count.ZERO;
        }
        if (!someValueLiesBetween(low, high)) {
            return null;
        }
        if (low == null) {
            return high == null ? Count.ZERO
                    : high.inclusive() ? high.at() : high.at().minus(1);
        }
        if (low.inclusive()) {
            return low.at();
        }
        // Open below, so the count is not the end. Halfway to the other end where there is one — a
        // count the dense carrier holds, and inside both — and a step in where there is not.
        return high == null ? low.at().plus(1) : low.at().halfwayTo(high.at(), Granularity.DENSE);
    }

    /** An end moved onto the nearest whole count the range holds, which is always one it holds. */
    private static Endpoint whole(Endpoint end, boolean lower) {
        if (end == null) {
            return null;
        }
        java.math.RoundingMode away = lower ? java.math.RoundingMode.CEILING
                : java.math.RoundingMode.FLOOR;
        if (end.inclusive()) {
            return inclusive(end.at().rounded(away));
        }
        java.math.RoundingMode into = lower ? java.math.RoundingMode.FLOOR
                : java.math.RoundingMode.CEILING;
        Count step = end.at().rounded(into);
        return inclusive(lower ? step.plus(1) : step.minus(1));
    }
}
