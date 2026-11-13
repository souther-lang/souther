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
 * <p>The coordinates are the positions in the order of the prefixes, the positions of the first
 * prefix first in the order the caller's {@link CanonicalOrder} puts them in, and each position is
 * the difference of its coordinate and the one before it. That is a change of basis of determinant
 * one over the whole numbers, so the rules in the new coordinates and the rules as they were have
 * the same whole-number solutions, each position being the same value read through it.
 *
 * <p>Chosen only where it comes to something the difference closure holds exactly: every rule is a
 * half-space, every position is a whole number, the rules' supports are prefixes one position
 * longer than the one before, every position is in a prefix, every number the change writes is one
 * the exact arithmetic holds, and every rule it writes is a bound on one coordinate or on the
 * difference of two. Where any of it is not so there is no basis, and the rules are closed as they
 * are stated. Which of two positions of the shortest prefix is the first is not the order the rules
 * arrived in, and does not change what any position is left.
 *
 * @param <A> what a position of the rules is
 */
final class PrefixBasis<A> {

    private static final CanonicalOrder<Integer> BY_PLACE = Integer::compare;

    /** The coordinate each position is the difference of with the one before it. */
    private final Map<A, Integer> places;

    /** The rules in the coordinates, their differences closed. */
    private final DifferenceBounds<Integer> closed;

    private PrefixBasis(Map<A, Integer> places, DifferenceBounds<Integer> closed) {
        this.places = places;
        this.closed = closed;
    }

    /**
     * How high a form comes to.
     *
     * @param at the cut, or null where nothing bounds the form above
     */
    record Highest(ExactCut at) {}

    /**
     * The basis the rules are read in, or null where they have none the difference closure holds
     * exactly.
     */
    static <A> PrefixBasis<A> over(List<AffineConstraint<A>> constraints,
                                   Function<A, Granularity> spacing, CanonicalOrder<A> order) {
        Set<Set<A>> distinct = new HashSet<>();
        List<Set<A>> supports = new ArrayList<>();
        List<List<Map.Entry<A, ExactRatio>>> walked = new ArrayList<>(constraints.size());
        for (AffineConstraint<A> rule : constraints) {
            if (!(rule instanceof AffineConstraint.HalfSpace<A> half)) {
                return null;
            }
            List<Map.Entry<A, ExactRatio>> entries = half.form().entriesIn(order);
            Set<A> support = new HashSet<>();
            for (Map.Entry<A, ExactRatio> each : entries) {
                if (spacing.apply(each.getKey()) != Granularity.DISCRETE) {
                    return null;
                }
                support.add(each.getKey());
            }
            walked.add(entries);
            if (support.size() >= 2 && distinct.add(support)) {
                supports.add(support);
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
        for (int at = 0; at < constraints.size(); at++) {
            AffineConstraint.HalfSpace<A> half =
                    (AffineConstraint.HalfSpace<A>) constraints.get(at);
            AffineConstraint.HalfSpace<Integer> there =
                    half(weighed(walked.get(at), places), half.bound());
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
        first.forEach(position -> places.put(position, places.size()));
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

    /**
     * What {@code weights} come to over the coordinates, or null where a position is in no prefix
     * or a number is not one the exact arithmetic holds. A weight on a position is a weight on its
     * coordinate and the opposite weight on the one before.
     */
    private static <A> Map<Integer, ExactRatio> weighed(Iterable<Map.Entry<A, ExactRatio>> weights,
                                                        Map<A, Integer> places) {
        Map<Integer, ExactRatio> out = new LinkedHashMap<>();
        for (Map.Entry<A, ExactRatio> each : weights) {
            Integer at = places.get(each.getKey());
            if (at == null || !added(out, at, each.getValue())
                    || (at > 0 && !added(out, at - 1, each.getValue().negated()))) {
                return null;
            }
        }
        out.values().removeIf(ExactRatio::isZero);
        return out;
    }

    private static boolean added(Map<Integer, ExactRatio> weights, int at, ExactRatio by) {
        ExactRatio now = weights.getOrDefault(at, ExactRatio.ZERO).plus(by).orNull();
        if (now == null) {
            return false;
        }
        weights.put(at, now);
        return true;
    }

    /** The rule {@code weights <= bound} over the coordinates, in lowest terms, or null. */
    private static AffineConstraint.HalfSpace<Integer> half(Map<Integer, ExactRatio> weights,
                                                            ExactCut bound) {
        if (weights == null
                || !(CanonicalForm.of(weights) instanceof CanonicalForm.Scaled<Integer> scaled)) {
            return null;
        }
        ExactRatio at = bound.at().dividedBy(scaled.by()).orNull();
        return at == null ? null
                : new AffineConstraint.HalfSpace<>(scaled.form(), new ExactCut(at, bound.inclusive()));
    }

    boolean holdsNothing() {
        return closed.holdsNothing();
    }

    /** Whether every hop of the difference closure was one the exact arithmetic could hold. */
    boolean everyHopWasComposed() {
        return closed.everyHopWasComposed();
    }

    /**
     * What each position is left, which is the whole of what the rules leave it: nothing sound
     * narrows a position this does not.
     */
    Box<A> box() {
        Map<A, ExactCut> least = new LinkedHashMap<>();
        Map<A, ExactCut> most = new LinkedHashMap<>();
        for (A position : places.keySet()) {
            ExactCut above = highest(Map.of(position, ExactRatio.ONE), ExactRatio.ZERO).at();
            ExactCut below = highest(Map.of(position, ExactRatio.ONE.negated()), ExactRatio.ZERO).at();
            if (above != null) {
                most.put(position, above);
            }
            if (below != null) {
                least.put(position, new ExactCut(below.at().negated(), below.inclusive()));
            }
        }
        return new Box<>(least, most);
    }

    /**
     * The highest {@code coefs} weighs, plus {@code constant}, or null where the form is not one
     * this answers: it is exact for a form that comes to one coordinate or to the difference of
     * two in the basis, such as a position or a prefix sum, and answers nothing else.
     *
     * <p>Exact because the closure of whole-number differences is: a bound it holds on a coordinate
     * or a difference is reached by a solution of the rules, so nothing sound bounds the form
     * lower. A bound the exact arithmetic could not hold is left out, which only leaves the answer
     * wider. Asked only where the rules leave something.
     */
    Highest highest(Map<A, ExactRatio> coefs, ExactRatio constant) {
        Map<Integer, ExactRatio> weights = weighed(coefs.entrySet(), places);
        if (weights == null) {
            return null;
        }
        List<Map.Entry<Integer, ExactRatio>> terms = new ArrayList<>(weights.entrySet());
        ExactCut bound;
        ExactRatio weight;
        if (terms.size() == 1) {
            weight = terms.getFirst().getValue();
            bound = weight.signum() > 0 ? closed.upperBoundOf(terms.getFirst().getKey())
                    : closed.lowerBoundOf(terms.getFirst().getKey());
        } else if (terms.size() == 2) {
            Map.Entry<Integer, ExactRatio> up = terms.getFirst();
            Map.Entry<Integer, ExactRatio> down = terms.getLast();
            if (up.getValue().signum() < 0) {
                up = terms.getLast();
                down = terms.getFirst();
            }
            weight = up.getValue();
            if (!weight.equals(down.getValue().negated())) {
                return null;
            }
            bound = closed.differenceBound(up.getKey(), down.getKey());
        } else {
            return null;
        }
        ExactRatio scaled = bound == null ? null : weight.times(bound.at()).orNull();
        ExactRatio at = scaled == null ? null : scaled.plus(constant).orNull();
        return new Highest(at == null ? null : new ExactCut(at, bound.inclusive()));
    }
}
