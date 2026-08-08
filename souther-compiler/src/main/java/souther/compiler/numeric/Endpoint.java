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
