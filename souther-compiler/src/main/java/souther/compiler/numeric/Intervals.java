package souther.compiler.numeric;

import java.math.BigDecimal;


/**
 * What arithmetic outside the affine fragment leaves of the ranges it was given.
 *
 * <p>{@link NumericDomain} relates positions linearly, and a product of two values and a quotient
 * are neither — so what they answer is one value the domain holds nothing about, however much it
 * holds about the values it was computed from. What is written here is the step from the one to the
 * other: given what is proven of the parts, what is proven of the whole.
 *
 * <p>Ranges in and a range out, and nothing else. A bound is read out of a domain and a bound is put
 * back into one, and both of those are the caller's; what is here is the arithmetic, which is where
 * the mistakes that matter live and is the only part that can be held to an answer written down.
 */
public final class Intervals {

    private Intervals() {}

    /**
     * What a product of two ranges lies between.
     *
     * <p>The four corner products, least and greatest. A product is bilinear, so nothing inside the
     * box reaches past what its corners do, and a range with an end nothing bounds is a corner at
     * infinity.
     *
     * <p>An end the product reaches is one some corner reaches, and it is asked of every corner
     * landing there rather than of the one that got there first: {@code [-1, 1] * [-1, 1]} reaches 1
     * at two corners, and a factor's end being open at one of them says nothing about the other.
     *
     * <p>Where an end is at zero the corners are not the whole of it. A product is bilinear, so it
     * is constant along the axis where a factor is zero: every value of one factor times zero is
     * zero, and zero is a value the product takes wherever <em>either</em> factor holds zero at all.
     * That is a value on an edge of the box and not at a corner of it, so a factor holding zero
     * strictly between its ends, or holding it at an end the other factor's ends do not pair with,
     * reaches zero all the same. {@code [0, 1] * (0, 1)} is {@code [0, 1)}, and read off the corners
     * alone it would come back open at an end it reaches.
     *
     * <p>Zero is not special in what the product's ends <em>are</em> — the corners give those — and
     * it is special in whether an end at zero is reached.
     */
    public static NumericDomain.Bounds product(NumericDomain.Bounds a, NumericDomain.Bounds b) {
        End belowA = End.below(a.min());
        End aboveA = End.above(a.max());
        End belowB = End.below(b.min());
        End aboveB = End.above(b.max());
        Corner[] corners = {
            belowA.times(belowB), belowA.times(aboveB),
            aboveA.times(belowB), aboveA.times(aboveB),
        };
        boolean zero = holdsZero(a, b) || holdsZero(b, a);
        return new NumericDomain.Bounds(furthest(corners, -1, zero), furthest(corners, 1, zero));
    }

    /** Whether {@code one} holds zero and {@code other} holds anything, which is what makes zero a
     * value the product takes. */
    private static boolean holdsZero(NumericDomain.Bounds one, NumericDomain.Bounds other) {
        return one.admits(Count.ZERO) && holdsAValue(other);
    }

    /** Whether a range holds any value at all. A range that holds none is not something a feasible
     * domain proves, and a product of one is not a value to say anything about. */
    private static boolean holdsAValue(NumericDomain.Bounds bounds) {
        return Endpoint.someValueLiesBetween(bounds.min(), bounds.max());
    }

    /**
     * What {@code x / k} lies between, given what {@code x} does and a written {@code k}.
     *
     * <p>Truncation toward zero is monotone — it never sends a larger dividend to a smaller
     * quotient — so the quotient's ends are the dividend's ends put through it, exchanged where the
     * divisor is negative and the order reverses with them. That is the whole rule: what it says is
     * about a sign and a magnitude and not an equation, which is why nothing linear could carry it.
     *
     * <p>An end the dividend does not reach is widened rather than sharpened. Truncation sends a
     * range of dividends onto one quotient, so an open end says nothing about whether the quotient
     * reaches what it lands on; a bound looser than the true one proves less and never rejects a
     * program the rules admit.
     *
     * @param divisor a whole number other than zero. What {@code /} does with a zero divisor is
     *                abort (spec §stdlib-int), and a bound on a value nothing computes is not a
     *                fact to derive.
     */
    public static NumericDomain.Bounds truncatingQuotient(NumericDomain.Bounds dividend,
                                                          long divisor) {
        if (divisor == 0) {
            throw new IllegalArgumentException("a quotient by zero is not a value to bound");
        }
        Endpoint low = truncated(dividend.min(), divisor);
        Endpoint high = truncated(dividend.max(), divisor);
        return divisor > 0 ? new NumericDomain.Bounds(low, high)
                : new NumericDomain.Bounds(high, low);
    }

    /** {@code end} divided by {@code divisor} and truncated toward zero, or null where the dividend
     * has no such end. */
    private static Endpoint truncated(Endpoint end, long divisor) {
        if (end == null) {
            return null;
        }
        BigDecimal quotient = Count.number(end.at()).at()
                .divide(BigDecimal.valueOf(divisor), 0, java.math.RoundingMode.DOWN);
        return Endpoint.inclusive(new Count(quotient));
    }

    /**
     * One end of one range, with the side it is on.
     *
     * <p>The side is what an end nothing bounds is: a range's lower end absent is every value below,
     * and its upper end absent is every value above. Held as an end rather than as a null, because
     * what an unbounded end multiplies to depends on which of the two it is — and a corner where two
     * of them meet has an answer, which is what reading them as one absent value cannot say.
     */
    private record End(Count at, boolean reached, int beyond) {

        static End below(Endpoint end) {
            return of(end, -1);
        }

        static End above(Endpoint end) {
            return of(end, 1);
        }

        private static End of(Endpoint end, int side) {
            return end == null ? new End(null, false, side)
                    : new End(Count.number(end.at()), end.inclusive(), 0);
        }

        /**
         * The corner this end makes with {@code other}.
         *
         * <p>An end past every value is not a number, so what it multiplies to is read off the other
         * end: zero against it is zero — every value times zero is zero, so the product is at zero
         * and reaches it exactly where that zero end is reached — and anything else is past every
         * value again, on the side the two signs give.
         */
        Corner times(End other) {
            if (beyond != 0 && other.beyond != 0) {
                return new Corner(null, false, beyond * other.beyond);
            }
            if (beyond != 0 || other.beyond != 0) {
                End finite = beyond != 0 ? other : this;
                End past = beyond != 0 ? this : other;
                if (finite.at.signum() == 0) {
                    return new Corner(Count.ZERO, finite.reached, 0);
                }
                return new Corner(null, false, past.beyond * finite.at.signum());
            }
            return new Corner(at.times(other.at.at()), reached && other.reached, 0);
        }
    }

    /**
     * One corner of the box two ranges make: what the two ends multiply to, whether the product has
     * a value there, and which side it is past every value on.
     */
    private record Corner(Count at, boolean reached, int beyond) {}

    /**
     * The corner furthest along {@code direction}, or null where the product runs past every value
     * that way.
     *
     * <p>Reached where any corner landing there is reached, and not where the first one to land
     * there was: two corners can multiply to one number, and one of them having an open end says
     * nothing about the other. An end at zero is reached where {@code zero} says the product takes
     * that value at all, which the corners are not the whole account of.
     */
    private static Endpoint furthest(Corner[] corners, int direction, boolean zero) {
        Count best = null;
        boolean reached = false;
        for (Corner corner : corners) {
            if (corner.beyond() == direction) {
                return null;
            }
            if (corner.at() == null) {
                continue;   // past every value the other way, which bounds nothing on this side
            }
            int order = best == null ? 1 : corner.at().compareTo(best) * direction;
            if (order > 0) {
                best = corner.at();
                reached = corner.reached();
            } else if (order == 0) {
                reached |= corner.reached();
            }
        }
        if (best == null) {
            return null;
        }
        return new Endpoint(best, reached || (zero && best.signum() == 0));
    }
}
