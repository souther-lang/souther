package souther.compiler.numeric;

import java.math.BigDecimal;

/** Where a range stops, and whether the value it stops at is one of its own. */
public record Endpoint(BigDecimal value, boolean inclusive) {

    public static Endpoint inclusive(BigDecimal value) {
        return new Endpoint(value, true);
    }

    public static Endpoint exclusive(BigDecimal value) {
        return new Endpoint(value, false);
    }

    /**
     * The tighter of two lower bounds, where a {@code null} is no bound and so never the tighter.
     *
     * <p>At one value the two are the same edge asked of two rules, and a conjunction cannot admit
     * what either conjunct refuses — so the value survives only where both admit it.
     */
    public static Endpoint lower(Endpoint a, Endpoint b) {
        if (a == null) {
            return b;
        }
        if (b == null) {
            return a;
        }
        int order = b.value().compareTo(a.value());
        if (order == 0) {
            return a.inclusive() && !b.inclusive() ? b : a;
        }
        return order > 0 ? b : a;
    }

    /**
     * Whether anything at all lies between a lower bound and an upper one, either of which may be
     * {@code null} for no bound.
     *
     * <p>Not a comparison of the two numbers. At one value they are equal whichever way they are
     * written, and what decides it is whether both admit that value — over a dense atom there is
     * nothing else between them to fall back on. A discrete atom never reaches here open: its strict
     * bounds are sharpened onto the adjacent value where they are recorded.
     */
    public static boolean someValueLiesBetween(Endpoint low, Endpoint high) {
        if (low == null || high == null) {
            return true;
        }
        int order = low.value().compareTo(high.value());
        if (order > 0) {
            return false;
        }
        return order < 0 || (low.inclusive() && high.inclusive());
    }

    /**
     * A value between a lower bound and an upper one, or {@code null} where they hold none.
     *
     * <p>The one way a pair of ends gives up a number, so that nothing deciding what to write reads
     * an end's value and loses whether the range holds it. An end the range holds is the value taken:
     * it is inside whatever other end there is, and it is the value a boundary wants written anyway.
     * An end the range stops short of is not one, and over a dense order there is no value beside it
     * to take instead — so the value comes from inside, between the ends where both are known and a
     * step in from the only one where there is one. Nothing about that step is the nearest value the
     * range holds; over a dense order there is no such thing. It is a value the range holds, chosen
     * the same way every time.
     *
     * <p>Over whole numbers each end moves onto the nearest whole number inside it first, which is
     * where a strict bound and a fractional one both become a value the type has.
     */
    public static BigDecimal valueBetween(Endpoint low, Endpoint high, Granularity spacing) {
        if (spacing == Granularity.DISCRETE) {
            Endpoint lo = whole(low, true);
            Endpoint hi = whole(high, false);
            if (!someValueLiesBetween(lo, hi)) {
                return null;
            }
            return lo != null ? lo.value() : hi != null ? hi.value() : BigDecimal.ZERO;
        }
        if (!someValueLiesBetween(low, high)) {
            return null;
        }
        if (low == null) {
            return high == null ? BigDecimal.ZERO
                    : high.inclusive() ? high.value() : high.value().subtract(BigDecimal.ONE);
        }
        if (low.inclusive()) {
            return low.value();
        }
        // Open below, so the value is not the end. Halfway to the other end where there is one — an
        // ordinary decimal, and inside both — and a step in where there is not.
        return high == null ? low.value().add(BigDecimal.ONE)
                : low.value().add(high.value()).divide(BigDecimal.valueOf(2));
    }

    /** An end moved onto the nearest whole number the range holds, which is always one it holds. */
    private static Endpoint whole(Endpoint end, boolean lower) {
        if (end == null) {
            return null;
        }
        java.math.RoundingMode away = lower ? java.math.RoundingMode.CEILING
                : java.math.RoundingMode.FLOOR;
        if (end.inclusive()) {
            return inclusive(end.value().setScale(0, away));
        }
        java.math.RoundingMode into = lower ? java.math.RoundingMode.FLOOR
                : java.math.RoundingMode.CEILING;
        BigDecimal step = end.value().setScale(0, into);
        return inclusive(lower ? step.add(BigDecimal.ONE) : step.subtract(BigDecimal.ONE));
    }

    /** The tighter of two upper bounds, the same way. */
    public static Endpoint upper(Endpoint a, Endpoint b) {
        if (a == null) {
            return b;
        }
        if (b == null) {
            return a;
        }
        int order = b.value().compareTo(a.value());
        if (order == 0) {
            return a.inclusive() && !b.inclusive() ? b : a;
        }
        return order < 0 ? b : a;
    }
}
