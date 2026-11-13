package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * Rules that are all sums of the same growing prefix, read in the coordinates where each of those
 * sums is one position.
 *
 * <p>A chain of {@code a_k = a_(k-1) + p_k} states, for every {@code k}, a bound on
 * {@code p_1 + ... + p_k} beside a bound on each {@code p_k}. Written over the {@code p}s every
 * sum names every position before it, and a reading that asks what the rest of a sum leaves has
 * a premise to look at for each of them. Written over {@code s_k = p_1 + ... + p_k} the same rules
 * are a bound on {@code s_k} and a bound on {@code s_k - s_(k-1)}: the shapes the difference
 * closure holds exactly, and which it closes without reading any rule against another.
 *
 * <p>The coordinates are the positions in the order of the prefixes, the first prefix's positions
 * first in the order the caller's {@link CanonicalOrder} puts them in, and each position is the
 * difference of its coordinate and the one before it. That is a change of basis of determinant one
 * over the whole numbers, so the rules in the new coordinates and the rules as they were have the
 * same whole-number solutions, each position being the same value read through it.
 *
 * <p>Chosen only where it comes to something this holds exactly: every rule is a half-space, every
 * position is a whole number, the rules' supports are prefixes one position longer than the one
 * before, every position is in a prefix, every number the change writes is one the exact arithmetic
 * holds, and every rule it writes is a bound on one coordinate or on the difference of two. Where
 * any of it is not so there is no basis, and the rules are closed as they are. Which of two positions
 * of the shortest prefix is the first is not the order the rules arrived in, and does not change
 * what any position is left.
 *
 * @param <A> what a position of the rules is
 */
final class PrefixBasis<A> {

    private static final CanonicalOrder<Integer> BY_PLACE = Integer::compare;

    /** The coordinate each position of the rules is the difference of with the one before it. */
    private final Map<A, Integer> places;

    /** The differences of the rules in the coordinates, closed. */
    private final DifferenceBounds<Integer> closed;

    private PrefixBasis(Map<A, Integer> places, DifferenceBounds<Integer> closed) {
        this.places = places;
        this.closed = closed;
    }

    /**
     * How high a form comes to, or that it is bounded nowhere above.
     *
     * @param at the cut, or null where nothing bounds the form above
     */
    record Highest(ExactCut at) {}

    /**
     * What the rules leave, read back to the positions they were stated over.
     *
     * @param box                   what each position is left, which is the whole of what the rules
     *                              leave it: nothing sound narrows a position this does not
     * @param holdsNothing          whether the rules leave nothing at all, which is decided and not
     *                              only proved
     * @param everyBoundWasComposed whether every hop of the difference closure was one the exact
     *                              arithmetic could hold
     */
    record Closure<A>(Box<A> box, boolean holdsNothing, boolean everyBoundWasComposed) {}

    /**
     * The basis the rules are read in, or null where they have none this holds exactly.
     *
     * @param spacing what each position is
     * @param order   the order the positions of a form are walked in
     */
    static <A> PrefixBasis<A> over(List<AffineConstraint<A>> constraints,
                                   Function<A, Granularity> spacing, CanonicalOrder<A> order) {
        Set<Set<A>> distinct = new HashSet<>();
        List<Set<A>> supports = new ArrayList<>();
        for (AffineConstraint<A> rule : constraints) {
            if (!(rule instanceof AffineConstraint.HalfSpace<A> half)) {
                return null;
            }
            List<A> support = half.form().atomsIn(order);
            for (A position : support) {
                if (spacing.apply(position) != Granularity.DISCRETE) {
                    return null;
                }
            }
            if (support.size() >= 2 && distinct.add(new HashSet<>(support))) {
                supports.add(new HashSet<>(support));
            }
        }
        if (supports.isEmpty()) {
            return null;
        }
        supports.sort((a, b) -> Integer.compare(a.size(), b.size()));
        for (int at = 1; at < supports.size(); at++) {
            if (supports.get(at).size() != supports.get(at - 1).size() + 1
                    || !supports.get(at).containsAll(supports.get(at - 1))) {
                return null;
            }
        }
        Map<A, Integer> places = placesOf(supports, order);
        if (places == null) {
            return null;
        }
        List<AffineConstraint<Integer>> moved = new ArrayList<>(constraints.size());
        for (AffineConstraint<A> rule : constraints) {
            AffineConstraint.HalfSpace<Integer> there = moved(rule, places, order);
            if (there == null || !DifferenceBounds.canHold(there, BY_PLACE)) {
                return null;
            }
            moved.add(there);
        }
        return new PrefixBasis<>(places, DifferenceBounds.over(moved, BY_PLACE));
    }

    /** The place of each position, or null where a position is in no prefix or two of the first
     *  prefix cannot be told apart. */
    private static <A> Map<A, Integer> placesOf(List<Set<A>> supports, CanonicalOrder<A> order) {
        Map<A, Integer> places = new HashMap<>();
        List<A> first = new ArrayList<>(supports.getFirst());
        first.sort(order);
        for (int at = 1; at < first.size(); at++) {
            if (order.compare(first.get(at - 1), first.get(at)) == 0) {
                return null;
            }
        }
        for (A position : first) {
            places.put(position, places.size());
        }
        for (Set<A> support : supports.subList(1, supports.size())) {
            A added = null;
            for (A position : support) {
                if (!places.containsKey(position)) {
                    added = position;
                }
            }
            if (added == null) {
                return null;
            }
            places.put(added, places.size());
        }
        return places;
    }

    /** {@code rule} over the coordinates, or null where a number it comes to is not one the exact
     *  arithmetic holds. */
    private static <A> AffineConstraint.HalfSpace<Integer> moved(AffineConstraint<A> rule,
                                                                 Map<A, Integer> places,
                                                                 CanonicalOrder<A> order) {
        AffineConstraint.HalfSpace<A> half = (AffineConstraint.HalfSpace<A>) rule;
        Map<Integer, ExactRatio> weights = new LinkedHashMap<>();
        for (Map.Entry<A, ExactRatio> each : half.form().entriesIn(order)) {
            Integer at = places.get(each.getKey());
            if (at == null || !weighed(weights, at, each.getValue())
                    || (at > 0 && !weighed(weights, at - 1, each.getValue().negated()))) {
                return null;
            }
        }
        if (!(CanonicalForm.of(weights) instanceof CanonicalForm.Scaled<Integer> scaled)) {
            return null;
        }
        ExactRatio at = half.bound().at().dividedBy(scaled.by()).orNull();
        if (at == null) {
            return null;
        }
        return new AffineConstraint.HalfSpace<>(scaled.form(),
                new ExactCut(at, half.bound().inclusive()));
    }

    private static boolean weighed(Map<Integer, ExactRatio> weights, int at, ExactRatio by) {
        ExactRatio now = weights.getOrDefault(at, ExactRatio.ZERO).plus(by).orNull();
        if (now == null) {
            return false;
        }
        weights.put(at, now);
        return true;
    }

    /** What the rules leave, from the closure of their differences in the coordinates. */
    Closure<A> close() {
        if (closed.holdsNothing()) {
            return new Closure<>(null, true, true);
        }
        Map<A, ExactCut> least = new LinkedHashMap<>();
        Map<A, ExactCut> most = new LinkedHashMap<>();
        for (Map.Entry<A, Integer> each : places.entrySet()) {
            int at = each.getValue();
            ExactCut above;
            ExactCut below;
            if (at == 0) {
                above = closed.upperBoundOf(0);
                below = closed.lowerBoundOf(0);
            } else {
                above = closed.differenceBound(at, at - 1);
                ExactCut under = closed.differenceBound(at - 1, at);
                below = under == null ? null : new ExactCut(under.at().negated(), under.inclusive());
            }
            if (above != null) {
                most.put(each.getKey(), above);
            }
            if (below != null) {
                least.put(each.getKey(), below);
            }
        }
        return new Closure<>(new Box<>(least, most), false, closed.everyHopWasComposed());
    }

    /**
     * The highest {@code coefs} weighs, plus {@code constant}, over the rules, or null where the
     * form is not one this answers: it is exact for a form that comes to one coordinate or to the
     * difference of two in the basis, such as a prefix sum or a position, and answers nothing
     * else.
     *
     * <p>Exact because the closure of whole-number differences is: a bound it holds on a coordinate
     * or a difference is reached by a solution of the rules, so nothing sound bounds the form
     * lower. Not answered where the closure could not sum a hop or the rules leave nothing.
     */
    Highest highest(Map<A, ExactRatio> coefs, ExactRatio constant) {
        if (closed.holdsNothing() || !closed.everyHopWasComposed()) {
            return null;
        }
        Map<Integer, ExactRatio> weights = new LinkedHashMap<>();
        for (Map.Entry<A, ExactRatio> each : coefs.entrySet()) {
            Integer at = places.get(each.getKey());
            if (at == null || !weighed(weights, at, each.getValue())
                    || (at > 0 && !weighed(weights, at - 1, each.getValue().negated()))) {
                return null;
            }
        }
        weights.values().removeIf(ExactRatio::isZero);
        ExactCut bound;
        ExactRatio weight;
        switch (weights.size()) {
            case 1 -> {
                Map.Entry<Integer, ExactRatio> only = weights.entrySet().iterator().next();
                weight = only.getValue();
                bound = weight.signum() > 0 ? closed.upperBoundOf(only.getKey())
                        : closed.lowerBoundOf(only.getKey());
            }
            case 2 -> {
                List<Map.Entry<Integer, ExactRatio>> two = new ArrayList<>(weights.entrySet());
                Map.Entry<Integer, ExactRatio> up = two.get(0);
                Map.Entry<Integer, ExactRatio> down = two.get(1);
                if (up.getValue().signum() < 0) {
                    up = two.get(1);
                    down = two.get(0);
                }
                weight = up.getValue();
                if (weight.signum() < 0 || !weight.equals(down.getValue().negated())) {
                    return null;
                }
                bound = closed.differenceBound(up.getKey(), down.getKey());
            }
            default -> {
                return null;
            }
        }
        if (bound == null) {
            return new Highest(null);
        }
        ExactRatio scaled = weight.times(bound.at()).orNull();
        ExactRatio at = scaled == null ? null : scaled.plus(constant).orNull();
        return at == null ? new Highest(null) : new Highest(new ExactCut(at, bound.inclusive()));
    }
}
