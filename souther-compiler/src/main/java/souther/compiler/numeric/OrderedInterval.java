package souther.compiler.numeric;

/**
 * What is left of one position's order once the rules about it have been taken in.
 *
 * <p>A pair of ends, either of which may be absent for no end there. Apart from
 * {@link NumericDomain.Bounds}, which holds the same two things and answers a different question:
 * that one is what a projection of the interval algebra left, and its {@code saysNothing} says that
 * nothing bounds the position at all. Here an empty interval is the opposite — a position the rules
 * leave no value at — and one type answering both would be a word that means "everything" to one
 * reader and "nothing" to the next.
 *
 * <p>Both ends are places on one order. Nothing here compares across two, and a pair built from two
 * scales' places says so by throwing where they are compared ({@link Place#notOneOrder}).
 */
public record OrderedInterval(Endpoint low, Endpoint high) {

    /** Every value of the order, for a scale that stops nowhere. */
    public static final OrderedInterval OPEN = new OrderedInterval(null, null);

    /**
     * Whether the rules leave this position no value.
     *
     * <p>Asked of the ends and not of the numbers between them. Over a scale whose values step, a
     * strict end is moved onto the value beside it where it is read, so what reaches here is two
     * ends and the question of whether anything is inside both.
     */
    public boolean holdsNothing() {
        return !Endpoint.someValueLiesBetween(low, high);
    }

    /**
     * Whether {@code at} is inside both ends.
     *
     * <p>Asked of the ends, because whether an end is one of the places it stops at is what the
     * place alone does not say.
     */
    public boolean admits(Place at) {
        return Endpoint.someValueLiesBetween(low, Endpoint.inclusive(at))
                && Endpoint.someValueLiesBetween(Endpoint.inclusive(at), high);
    }

    /** Both, which is what a conjunction of rules leaves: a value inside this one and inside the
     *  other. */
    public OrderedInterval meet(OrderedInterval other) {
        return new OrderedInterval(Endpoint.lower(low, other.low),
                Endpoint.upper(high, other.high));
    }

    /**
     * Either, as far as a pair of ends can say it.
     *
     * <p>The hull and not the union. A choice between two ranges is not a range where they do not
     * touch, and the ends around both admit everything either of them does — which is the safe
     * direction here, since what this decides is that a position has no value.
     *
     * <p>An empty side contributes no value to the hull, so the hull of one with a non-empty side is
     * the other side. Hulled as ends instead, an empty range would stretch the answer over values
     * neither side holds — its ends are places on the order all the same, and nothing lies between
     * them.
     *
     * <p>Whether an alternative is one anybody can take is not asked here, and not by
     * {@link OrderedIntervals} either. That is about a whole reading of a clause, which is more than
     * the ranges: it is settled where the languages a clause is read in are held together, and what
     * reaches this is one position of a branch whose fate is known.
     */
    public OrderedInterval join(OrderedInterval other) {
        if (holdsNothing()) {
            return other;
        }
        if (other.holdsNothing()) {
            return this;
        }
        return new OrderedInterval(widest(low, other.low, true),
                widest(high, other.high, false));
    }

    /** The looser of two ends, a {@code null} being no end at all and so the loosest there is. */
    private static Endpoint widest(Endpoint a, Endpoint b, boolean lower) {
        if (a == null || b == null) {
            return null;
        }
        Endpoint tighter = lower ? Endpoint.lower(a, b) : Endpoint.upper(a, b);
        return tighter.equals(a) ? b : a;
    }
}
