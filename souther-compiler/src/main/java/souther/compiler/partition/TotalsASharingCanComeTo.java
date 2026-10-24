package souther.compiler.partition;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

/**
 * The totals a container can come to when its elements are shared out among kinds, each kind
 * leaving its elements an interval of numbers that moves with the total.
 *
 * <p>With the total fixed, a kind leaves an element the numbers between the greatest of some
 * lower bounds and the least of some upper bounds, each a line in the total ({@link Line}). A
 * container of so many elements of each kind comes to the total where every kind leaves its
 * elements some number there ({@link #whereAnElementCanBe}) and the total is between the least and
 * the greatest those intervals sum to. The least the elements can sum to is a sum of greatests of
 * lines, which is convex in the total, and the greatest a sum of leasts, which is concave; so the
 * totals that are between them are one interval over the rationals, and so is the set of totals
 * a kind leaves some number at, and the two meet in one.
 *
 * <p>Exactly that interval, found by looking at the totals where one line of a kind passes
 * another: between two of them every sum is a line, and a line meets nought at one place. This
 * costs the lines of each kind and no more for how many kinds there are, where putting the bounds
 * together to eliminate each kind's numbers one after another multiplies them.
 *
 * <p>The ends are closed. A bound that holds only strictly is taken as if it held with equality,
 * so the interval may hold a total no whole number elements meet; the caller reads the intervals
 * at each whole number it tries, which is exact.
 */
final class TotalsASharingCanComeTo {

    /** A bound on an element's number, {@code slope · total + intercept}. */
    record Line(ExactRatio slope, ExactRatio intercept) {}

    /**
     * What a kind leaves its elements.
     *
     * @param lower     the numbers an element is at least; none where it may be any below
     * @param upper     the numbers an element is at most; none where it may be any above
     * @param totalLow  the least total the kind allows, or null where it allows any
     * @param totalHigh the greatest total the kind allows, or null where it allows any
     */
    record Reach(List<Line> lower, List<Line> upper, ExactRatio totalLow, ExactRatio totalHigh) {

        Reach {
            lower = List.copyOf(lower);
            upper = List.copyOf(upper);
        }
    }

    /** The totals, either end missing where they run on without end. */
    record Interval(ExactRatio low, ExactRatio high) {}

    /**
     * The whole numbers of an interval that were taken to be tried.
     *
     * @param tried the nearest nought first, then about each end
     * @param all   whether they are every whole number the interval holds
     */
    record WholeNumbers(List<BigInteger> tried, boolean all) {

        WholeNumbers {
            tried = List.copyOf(tried);
        }
    }

    /**
     * At most {@code limit} whole numbers of {@code span}: the one nearest nought, and the ones
     * about it and about each end the interval has, the nearest first. Where the interval holds
     * no whole number, none are tried and that is all of them.
     */
    static WholeNumbers wholeNumbersIn(Interval span, int limit) {
        BigInteger low = null;
        BigInteger high = null;
        if (span.low() != null) {
            if (!(span.low().ceiling() instanceof ExactAnswer.Held<BigInteger>(var up))) {
                return new WholeNumbers(List.of(), false);
            }
            low = up;
        }
        if (span.high() != null) {
            if (!(span.high().floor() instanceof ExactAnswer.Held<BigInteger>(var down))) {
                return new WholeNumbers(List.of(), false);
            }
            high = down;
        }
        if (low != null && high != null && low.compareTo(high) > 0) {
            return new WholeNumbers(List.of(), true);
        }
        BigInteger nearest = BigInteger.ZERO;
        if (low != null && nearest.compareTo(low) < 0) {
            nearest = low;
        }
        if (high != null && nearest.compareTo(high) > 0) {
            nearest = high;
        }
        Set<BigInteger> out = new LinkedHashSet<>();
        BigInteger[] bases = {nearest, low, high};
        for (int away = 0; away <= limit && out.size() < limit; away++) {
            for (BigInteger base : bases) {
                if (base == null) {
                    continue;
                }
                for (int sign = 1; sign >= -1; sign -= 2) {
                    BigInteger at = base.add(BigInteger.valueOf((long) sign * away));
                    if ((low == null || at.compareTo(low) >= 0)
                            && (high == null || at.compareTo(high) <= 0)
                            && out.size() < limit) {
                        out.add(at);
                    }
                }
            }
        }
        boolean every = low != null && high != null
                && high.subtract(low).add(BigInteger.ONE).compareTo(BigInteger.valueOf(limit)) <= 0;
        return new WholeNumbers(new ArrayList<>(out), every);
    }

    private final Set<CompositionCapacity> unheld;
    private boolean unholdable;

    private TotalsASharingCanComeTo(Set<CompositionCapacity> unheld) {
        this.unheld = unheld;
    }

    /**
     * The totals at which a kind leaves an element some number: where its greatest lower bound is
     * no greater than its least upper bound. Each pair of a lower and an upper line is a bound on
     * the total of its own.
     *
     * @return null where there are none, or where the exact arithmetic could not hold what it
     *         worked out (said in {@code unheld})
     */
    static Interval whereAnElementCanBe(Reach reach, Set<CompositionCapacity> unheld) {
        TotalsASharingCanComeTo search = new TotalsASharingCanComeTo(unheld);
        ExactRatio low = reach.totalLow();
        ExactRatio high = reach.totalHigh();
        for (Line lower : reach.lower()) {
            for (Line upper : reach.upper()) {
                ExactRatio slope = search.held(lower.slope().minus(upper.slope()));
                ExactRatio intercept = search.held(lower.intercept().minus(upper.intercept()));
                if (slope.isZero()) {
                    if (intercept.signum() > 0) {
                        return null;
                    }
                    continue;
                }
                // slope · total + intercept <= 0
                ExactRatio edge = search.held(intercept.negated().dividedBy(slope));
                if (slope.signum() > 0) {
                    high = tighter(high, edge, false);
                } else {
                    low = tighter(low, edge, true);
                }
            }
        }
        if (search.unholdable || (low != null && high != null && low.compareTo(high) > 0)) {
            return null;
        }
        return new Interval(low, high);
    }

    /**
     * The totals a container of {@code counts[i]} elements of kind {@code reaches[i]}, for each i,
     * can come to — or null where there are none, or where the exact arithmetic could not hold
     * what it worked out (said in {@code unheld}).
     */
    static Interval of(List<Reach> reaches, int[] counts, Set<CompositionCapacity> unheld) {
        TotalsASharingCanComeTo search = new TotalsASharingCanComeTo(unheld);
        Interval found = search.search(reaches, counts);
        return search.unholdable ? null : found;
    }

    private ExactRatio held(ExactAnswer<ExactRatio> answer) {
        return switch (answer) {
            case ExactAnswer.Held<ExactRatio>(ExactRatio value) -> value;
            case ExactAnswer.Unheld<ExactRatio>(var why) -> {
                unheld.add(new CompositionCapacity(
                        CompositionCapacity.Where.VALUES_A_TOTAL_IS_SPREAD_OVER, why));
                unholdable = true;
                yield ExactRatio.ZERO;
            }
        };
    }

    private Interval search(List<Reach> reaches, int[] counts) {
        ExactRatio low = null;
        ExactRatio high = null;
        TreeSet<ExactRatio> places = new TreeSet<>();
        for (Reach each : reaches) {
            // A kind has an element only at the totals where its least is no more than its
            // greatest; at any other the sums of the kinds say nothing, since a kind with none
            // adds none.
            // A kind has an element only at the totals where its least is no more than its
            // greatest; at any other the sums of the kinds say nothing, since a kind with none
            // adds none.
            Interval inhabited = whereAnElementCanBe(each, unheld);
            if (inhabited == null) {
                return null;
            }
            low = tighter(low, inhabited.low(), true);
            high = tighter(high, inhabited.high(), false);
            crossings(each.lower(), places);
            crossings(each.upper(), places);
        }
        if (low != null) {
            places.add(low);
        }
        if (high != null) {
            places.add(high);
        }
        if (unholdable || (low != null && high != null && low.compareTo(high) > 0)) {
            return null;
        }
        List<ExactRatio> cuts = new ArrayList<>(places);
        Interval hull = null;
        // The totals before the first place, between each two, and after the last: on each, what
        // the elements can sum to is a line at either end, so the sample totals are two on it.
        for (int part = 0; part <= cuts.size(); part++) {
            ExactRatio from = part == 0 ? null : cuts.get(part - 1);
            ExactRatio to = part == cuts.size() ? null : cuts.get(part);
            Interval here = within(reaches, counts, from, to, low, high);
            if (unholdable) {
                return null;
            }
            if (here != null) {
                hull = hull == null ? here : new Interval(
                        hull.low() == null || here.low() == null ? null
                                : hull.low().compareTo(here.low()) <= 0 ? hull.low() : here.low(),
                        hull.high() == null || here.high() == null ? null
                                : hull.high().compareTo(here.high()) >= 0 ? hull.high()
                                        : here.high());
            }
        }
        return hull;
    }

    private static ExactRatio tighter(ExactRatio one, ExactRatio other, boolean greater) {
        if (one == null || other == null) {
            return one == null ? other : one;
        }
        return (other.compareTo(one) > 0) == greater ? other : one;
    }

    /** The totals at which two lines of one list are one. */
    private void crossings(List<Line> lines, Set<ExactRatio> into) {
        for (int one = 0; one < lines.size(); one++) {
            for (int other = one + 1; other < lines.size(); other++) {
                ExactRatio apart = held(lines.get(one).slope().minus(lines.get(other).slope()));
                if (!apart.isZero()) {
                    into.add(held(held(lines.get(other).intercept()
                            .minus(lines.get(one).intercept())).dividedBy(apart)));
                }
            }
        }
    }

    /** The totals in [from, to] where the sharing's elements can come to the total. */
    private Interval within(List<Reach> reaches, int[] counts, ExactRatio from, ExactRatio to,
                            ExactRatio low, ExactRatio high) {
        ExactRatio first;
        ExactRatio second;
        if (from != null && to != null) {
            first = from;
            second = to;
        } else if (from != null) {
            first = held(from.plus(ExactRatio.ONE));
            second = held(from.plus(ExactRatio.of(2)));
        } else if (to != null) {
            first = held(to.minus(ExactRatio.of(2)));
            second = held(to.minus(ExactRatio.ONE));
        } else {
            first = ExactRatio.ZERO;
            second = ExactRatio.ONE;
        }
        Interval out = new Interval(from, to);
        ExactRatio[] atFirst = roomsAt(reaches, counts, first);
        ExactRatio[] atSecond = roomsAt(reaches, counts, second);
        for (int room = 0; room < 2; room++) {
            out = meet(out, atFirst[room], first, atSecond[room], second);
            if (out == null) {
                return null;
            }
        }
        return clip(out, low, high);
    }

    private static Interval clip(Interval span, ExactRatio low, ExactRatio high) {
        ExactRatio from = tighter(span.low(), low, true);
        ExactRatio to = tighter(span.high(), high, false);
        return from != null && to != null && from.compareTo(to) > 0 ? null
                : new Interval(from, to);
    }

    /**
     * The totals of {@code span} where a room that is {@code firstRoom} at {@code first} and
     * {@code secondRoom} at {@code second}, and a line between, is at least nought — or null where
     * there are none. A room that is null is one nothing bounds.
     */
    private Interval meet(Interval span, ExactRatio firstRoom, ExactRatio first,
                          ExactRatio secondRoom, ExactRatio second) {
        if (firstRoom == null || secondRoom == null) {
            return span;
        }
        ExactRatio slope = held(held(secondRoom.minus(firstRoom)).dividedBy(
                held(second.minus(first))));
        if (slope.isZero()) {
            return firstRoom.signum() >= 0 ? span : null;
        }
        // room(total) = firstRoom + slope · (total − first) ≥ 0
        ExactRatio edge = held(first.minus(held(firstRoom.dividedBy(slope))));
        Interval half = slope.signum() > 0 ? new Interval(edge, null) : new Interval(null, edge);
        ExactRatio from = tighter(span.low(), half.low(), true);
        ExactRatio to = tighter(span.high(), half.high(), false);
        return from != null && to != null && from.compareTo(to) > 0 ? null
                : new Interval(from, to);
    }

    /**
     * How far above the least, and below the greatest, the elements can sum to the total is —
     * each null where nothing bounds the sum on that side.
     */
    private ExactRatio[] roomsAt(List<Reach> reaches, int[] counts, ExactRatio total) {
        ExactRatio least = ExactRatio.ZERO;
        ExactRatio most = ExactRatio.ZERO;
        boolean leastKnown = true;
        boolean mostKnown = true;
        for (int at = 0; at < reaches.size(); at++) {
            ExactRatio count = ExactRatio.of(counts[at]);
            Reach reach = reaches.get(at);
            if (reach.lower().isEmpty()) {
                leastKnown = false;
            } else if (leastKnown) {
                least = held(least.plus(held(count.times(extreme(reach.lower(), total, true)))));
            }
            if (reach.upper().isEmpty()) {
                mostKnown = false;
            } else if (mostKnown) {
                most = held(most.plus(held(count.times(extreme(reach.upper(), total, false)))));
            }
        }
        return new ExactRatio[] {leastKnown ? held(total.minus(least)) : null,
                mostKnown ? held(most.minus(total)) : null};
    }

    /** The greatest of the lines at the total, or the least. */
    private ExactRatio extreme(List<Line> lines, ExactRatio total, boolean greatest) {
        ExactRatio out = null;
        for (Line each : lines) {
            ExactRatio at = held(held(each.slope().times(total)).plus(each.intercept()));
            if (out == null || (at.compareTo(out) > 0) == greatest) {
                out = at;
            }
        }
        return out;
    }
}
