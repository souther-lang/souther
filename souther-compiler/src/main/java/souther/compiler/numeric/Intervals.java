package souther.compiler.numeric;

import java.math.RoundingMode;


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
        return one.admits(Count.ZERO) && other.holdsAValue();
    }

    /**
     * What {@code x / y} lies between, given what each of them does.
     *
     * <p><b>What this bounds is the values the operation produces.</b> {@code /} over whole numbers
     * does not answer everywhere, and one of the pairs it aborts on lies inside ranges this is asked
     * about: {@code Long.MIN_VALUE} over {@code -1} is a quotient no {@code Int} holds (spec
     * §stdlib-int), and both of its operands are ordinary values of their type. That pair leaves no
     * value, so what comes back is a range of what the successful divides came to and nothing else.
     * What a caller must not read into it is the other thing: a range coming back — top included —
     * does not say the operation answers for every pair the two ranges admit. Whether it does is a
     * different question with a different answer, and answering it here would be an interval that
     * means two things.
     *
     * <p><b>The corners, and the corners are the whole of it.</b> A divisor range held away from
     * zero is of one sign throughout, and over such a range the divide is monotone along each
     * operand with the other held — in a direction that may turn with the other's sign, which is why
     * the corners and not a direction are what this is written about. Taking the ends of one operand
     * first and then of the other leaves the extremes at the four corners, and truncation toward zero
     * is non-decreasing, so putting the corners through it after keeps them the extremes.
     *
     * <p><b>A corner extended arithmetic gives no value is not a candidate.</b> An end past every
     * value divided by another such end is no number, and the hull is taken over the corners that
     * are numbers. Nothing is lost by it: a divisor away from zero has at most one end past every
     * value — both would be a range through zero — so the dividend end that met it also meets the
     * divisor's other, finite end, and reaches the same side there.
     *
     * <p>An end an operand does not reach is widened rather than sharpened. Truncation sends a range
     * of dividends onto one quotient, so an open end says nothing about whether the quotient reaches
     * what it lands on; a bound looser than the true one proves less and never rejects a program the
     * rules admit.
     *
     * @param divisor a range holding at least one value and none of them zero. Both are the caller's
     *                to establish ({@code DerivedNumericFacts}), and neither could be answered here as a
     *                range: a range with nothing in it is not a divisor whose sign and magnitude
     *                could be read, and what a range admitting zero leaves depends on how its values
     *                are spaced, which is not something a range says. Over the whole numbers a
     *                divisor between zero and five divides by one at the nearest, and the quotients
     *                are bounded; over a dense order there is no nearest and they are not. A caller
     *                that has a divisor it cannot hold off zero has a rule that does not apply, and
     *                answering that here would put it in the same value as a bound.
     */
    public static NumericDomain.Bounds truncatingQuotient(NumericDomain.Bounds dividend,
                                                          NumericDomain.Bounds divisor) {
        if (!divisor.holdsAValue()) {
            throw new IllegalArgumentException("a range holding no value is not a divisor to read");
        }
        if (divisor.admits(Count.ZERO)) {
            throw new IllegalArgumentException("a range admitting zero is not a divisor to read");
        }
        End belowX = End.below(dividend.min());
        End aboveX = End.above(dividend.max());
        End belowY = End.below(divisor.min());
        End aboveY = End.above(divisor.max());
        int sign = signOf(divisor);
        Ratio[] corners = {
            belowX.over(belowY, sign), belowX.over(aboveY, sign),
            aboveX.over(belowY, sign), aboveX.over(aboveY, sign),
        };
        return new NumericDomain.Bounds(hull(corners, -1), hull(corners, 1));
    }

    /**
     * Which side of zero a range held away from it lies on.
     *
     * <p>Read off the lower end, which says it or is absent — a range with none runs below every
     * value and holds zero unless it stops before it. Zero itself decides nothing by being there:
     * a lower end <em>at</em> zero belongs to a range held away from zero only by not being one of
     * its own values, and then everything above it is.
     */
    private static int signOf(NumericDomain.Bounds divisor) {
        Endpoint low = divisor.min();
        if (low == null) {
            return -1;
        }
        int side = Count.number(low.at()).signum();
        return side > 0 || (side == 0 && !low.inclusive()) ? 1 : -1;
    }

    /** The end of the quotient furthest along {@code direction}, or null where it runs past every
     * value that way. Taken over the corners that are numbers, and inclusive because an end this
     * lands on is widened rather than sharpened. */
    private static Endpoint hull(Ratio[] corners, int direction) {
        Count best = null;
        for (Ratio corner : corners) {
            if (corner == null) {
                continue;   // extended arithmetic gives this pair of ends no value
            }
            if (corner.beyond() == direction) {
                return null;
            }
            if (corner.at() == null) {
                continue;   // past every value the other way, which bounds nothing on this side
            }
            if (best == null || corner.at().compareTo(best) * direction > 0) {
                best = corner.at();
            }
        }
        return best == null ? null : Endpoint.inclusive(best);
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

        /**
         * The corner this end makes with {@code divisor}, or null where extended arithmetic gives
         * the pair no value.
         *
         * <p>{@code sign} is which side of zero the whole divisor range lies on, which its ends do
         * not each say: an end at zero belongs to a range held away from it only by not being one of
         * its own values, and what a divisor just past that end divides to is decided by the side
         * the range is on.
         *
         * <p>Two ends past every value are the pair with no value — how fast each of them runs out
         * is not something a range says, so their ratio is no number. Every other pair has one: a
         * divisor past every value sends any dividend to zero; a divisor as near zero as its range
         * allows sends any dividend but zero past every value; and zero divided by anything is zero.
         */
        Ratio over(End divisor, int sign) {
            if (beyond != 0 && divisor.beyond != 0) {
                return null;
            }
            if (divisor.beyond != 0) {
                return new Ratio(Count.ZERO, 0);
            }
            if (at != null && at.signum() == 0) {
                return new Ratio(Count.ZERO, 0);
            }
            if (divisor.at.signum() == 0) {
                return new Ratio(null, (beyond != 0 ? beyond : at.signum()) * sign);
            }
            if (beyond != 0) {
                return new Ratio(null, beyond * divisor.at.signum());
            }
            return new Ratio(Count.of(at.at().divide(divisor.at.at(), 0, RoundingMode.DOWN)), 0);
        }
    }

    /**
     * One corner of the box a dividend range and a divisor range make: what the two ends divide to,
     * or which side it is past every value on.
     *
     * <p>Without whether the quotient reaches it. Truncation sends a range of dividends onto one
     * quotient, so an end an operand does not reach says nothing about whether the quotient reaches
     * where it lands — and a bound that says it does is the looser of the two, which is the one to
     * state.
     */
    private record Ratio(Count at, int beyond) {}

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
