package souther.compiler.numeric;

/**
 * Where a constraint stops, exactly, and whether the value it stops at is one it admits.
 *
 * <p>The same shape as {@link Endpoint} and not the same thing. An endpoint is where a range stops
 * on a carrier's order and is spelled in the decimals a carrier counts in; this is where the algebra
 * stops while it is still reasoning, and is spelled in {@link Rational} because that is what
 * dividing produces. One becomes the other once, at the edge where a bound is handed to a reader.
 *
 * <p>One type for both of the algebra's bounds. A bound on a position and a bound on the difference
 * of two of them are the same statement — a value and whether it is reached — so the rules for
 * composing them get written once rather than once per bound.
 */
public record RationalCut(Rational at, boolean inclusive) {

    public RationalCut {
        if (at == null) {
            throw new IllegalArgumentException("a cut stops at a value; use null for no cut");
        }
    }

    public static RationalCut inclusive(Rational at) {
        return new RationalCut(at, true);
    }

    public static RationalCut exclusive(Rational at) {
        return new RationalCut(at, false);
    }

    /**
     * The two cuts added, admitting its own value only where both do.
     *
     * <p>What composing two hops is: {@code a - b <= c} with {@code b - d <= e} bounds {@code a - d}
     * at {@code c + e}, and the sum is reached only by a pair that reaches both. Written once here
     * rather than at each place a path is walked, because the strictness is the half that gets
     * dropped — a path summing to a bound its hops cannot both reach still bounds, and calling it
     * reachable puts a row at a pair nothing can be.
     */
    public static RationalCut meetingBoth(RationalCut a, RationalCut b) {
        return new RationalCut(a.at.plus(b.at), a.inclusive && b.inclusive);
    }

    /**
     * The tighter of two lower bounds, where {@code null} is no bound and so never the tighter.
     *
     * <p>Its own method because which of two values is the tighter runs the other way here: above,
     * the smaller value; below, the larger. Whether the value itself is admitted does not run the
     * other way — an exclusive cut admits less on either side and is the tighter of the two on
     * either side — so an order over cuts alone would be right about the strictness and wrong about
     * the value, on one side or the other, however it was written.
     */
    public static RationalCut tighterLower(RationalCut a, RationalCut b) {
        if (a == null || b == null) {
            return a == null ? b : a;
        }
        int order = a.at.compareTo(b.at);
        if (order == 0) {
            return a.inclusive ? b : a;
        }
        return order > 0 ? a : b;
    }

    /**
     * The tighter of two upper bounds, where {@code null} is no bound and so never the tighter.
     *
     * <p>At one value the two are one edge asked of two rules, and a conjunction admits only what
     * both admit — so the value survives only where neither excludes it.
     *
     * <p>Named for the side it is about, and this type is not {@link Comparable}: see
     * {@link #tighterLower} for which half of the comparison depends on the side and which does not.
     */
    public static RationalCut tighterUpper(RationalCut a, RationalCut b) {
        if (a == null || b == null) {
            return a == null ? b : a;
        }
        int order = a.at.compareTo(b.at);
        if (order == 0) {
            return a.inclusive ? b : a;
        }
        return order < 0 ? a : b;
    }

    @Override
    public String toString() {
        return (inclusive ? "<= " : "< ") + at;
    }
}
