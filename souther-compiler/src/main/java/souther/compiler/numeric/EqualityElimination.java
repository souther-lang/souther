package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A sum written over the positions the equalities leave free, where the rules hold equalities over
 * several of them.
 *
 * <p>A goal {@code F} and an equality {@code R = b} are the same goal as {@code F - m·(R - b)} for
 * any {@code m}, so a goal may be asked in whichever of those writings the rules prove. Chosen here
 * is the one with no position that an equality could be solved for: each equality is solved for the
 * last of its positions in the order the domain walks them, and a position solved for is put in
 * terms of the rest wherever it appears. The writing is then the same whichever order the
 * equalities were said in. A query that takes one rule as its premise ({@link ClosedState}) finds
 * in it what it would have needed two rules to find in the first — {@code x = a + b} beside
 * {@code y = b + a} proves {@code x - y} is nought.
 *
 * <p>Asked after the goal as written has not been proven, never in place of it: the writing here is
 * equal to the first wherever the equalities hold, so what it proves is proven, and when it does
 * not prove the goal nothing was lost. Arithmetic the exact numbers cannot hold ends the
 * elimination, and the goal stays as it was.
 */
final class EqualityElimination<A> {

    /** A goal in the writing the equalities leave. */
    record Goal<A>(Map<A, ExactRatio> coefs, ExactRatio constant) {}

    /** An equality solved for {@code pivot}: {@code pivot + Σ rest = at}. */
    private record Solved<A>(A pivot, Map<A, ExactRatio> rest, ExactRatio at) {}

    private final CanonicalOrder<A> order;
    private final Set<A> inTheGoal;
    private final List<Solved<A>> solved = new ArrayList<>();

    private EqualityElimination(CanonicalOrder<A> order, Set<A> inTheGoal) {
        this.order = order;
        this.inTheGoal = inTheGoal;
    }

    /**
     * {@code goal} in terms of the positions {@code equalities} leave free, or null where that is
     * the goal as it was or the arithmetic could not hold it.
     */
    static <A> Goal<A> through(List<AffineConstraint.Equality<A>> equalities, Goal<A> goal,
                               CanonicalOrder<A> order) {
        List<AffineConstraint.Equality<A>> joined =
                joinedTo(goal.coefs().keySet(), equalities, order);
        // What the domain holds exactly already is a difference of two positions: a goal joined
        // to nothing else is asked of it as it stands.
        if (joined.stream().allMatch(each -> DifferenceBounds.holdsExactly(each, order))) {
            return null;
        }
        EqualityElimination<A> elimination =
                new EqualityElimination<>(order, goal.coefs().keySet());
        for (AffineConstraint.Equality<A> each : joined) {
            if (!elimination.take(each)) {
                return null;
            }
        }
        if (elimination.solved.isEmpty()) {
            return null;
        }
        Goal<A> out = elimination.put(goal);
        boolean asItWas = out != null && out.coefs().equals(goal.coefs())
                && out.constant().equals(goal.constant());
        return out == null || asItWas ? null : out;
    }

    /**
     * The equalities that name a position of the goal, or a position another of them names that
     * does: an equality over positions the goal never reaches cannot change how it is written.
     */
    private static <A> List<AffineConstraint.Equality<A>> joinedTo(
            Set<A> reached, List<AffineConstraint.Equality<A>> equalities, CanonicalOrder<A> order) {
        Set<A> positions = new HashSet<>(reached);
        List<AffineConstraint.Equality<A>> joined = new ArrayList<>();
        List<AffineConstraint.Equality<A>> rest = new ArrayList<>(equalities);
        for (boolean grew = true; grew; ) {
            grew = false;
            for (var each = rest.iterator(); each.hasNext(); ) {
                AffineConstraint.Equality<A> equality = each.next();
                List<A> named = equality.form().atomsIn(order);
                if (!Collections.disjoint(positions, named)) {
                    positions.addAll(named);
                    joined.add(equality);
                    each.remove();
                    grew = true;
                }
            }
        }
        return joined;
    }

    /** Solves {@code equality} for one position, after putting the ones already solved in terms of
     *  the rest. False where the arithmetic could not hold it. */
    private boolean take(AffineConstraint.Equality<A> equality) {
        Map<A, ExactRatio> said = new LinkedHashMap<>();
        for (Map.Entry<A, ExactRatio> each : equality.form().entriesIn(order)) {
            said.put(each.getKey(), each.getValue());
        }
        Goal<A> as = put(new Goal<>(said, equality.at().negated()));
        if (as == null) {
            return false;
        }
        List<Map.Entry<A, ExactRatio>> walked = walked(as.coefs());
        if (walked.isEmpty()) {
            return true;   // said already, or said against itself: nothing to solve for
        }
        Map.Entry<A, ExactRatio> last = walked.getLast();
        A pivot = last.getKey();
        Map<A, ExactRatio> rest = new LinkedHashMap<>();
        for (Map.Entry<A, ExactRatio> entry : walked) {
            if (!entry.getKey().equals(pivot)) {
                ExactRatio scaled = entry.getValue().dividedBy(last.getValue()).orNull();
                if (scaled == null) {
                    return false;
                }
                rest.put(entry.getKey(), scaled);
            }
        }
        ExactRatio at = as.constant().negated().dividedBy(last.getValue()).orNull();
        if (at == null) {
            return false;
        }
        Solved<A> fresh = new Solved<>(pivot, rest, at);
        List<Solved<A>> kept = new ArrayList<>();
        for (Solved<A> old : solved) {
            Goal<A> in = putFor(old, fresh);
            if (in == null) {
                return false;
            }
            kept.add(new Solved<>(old.pivot(), in.coefs(), in.constant()));
        }
        solved.clear();
        solved.addAll(kept);
        solved.add(fresh);
        return true;
    }

    /** {@code old}'s right-hand side with {@code fresh}'s position put in terms of the rest. */
    private Goal<A> putFor(Solved<A> old, Solved<A> fresh) {
        ExactRatio weight = old.rest().get(fresh.pivot());
        if (weight == null) {
            return new Goal<>(old.rest(), old.at());
        }
        Map<A, ExactRatio> rest = new LinkedHashMap<>(old.rest());
        rest.remove(fresh.pivot());
        for (Map.Entry<A, ExactRatio> entry : walked(fresh.rest())) {
            ExactRatio moved = weight.times(entry.getValue()).orNull();
            ExactRatio had = rest.getOrDefault(entry.getKey(), ExactRatio.ZERO);
            ExactRatio now = moved == null ? null : had.minus(moved).orNull();
            if (now == null) {
                return null;
            }
            if (now.isZero()) {
                rest.remove(entry.getKey());
            } else {
                rest.put(entry.getKey(), now);
            }
        }
        ExactRatio taken = weight.times(fresh.at()).orNull();
        ExactRatio at = taken == null ? null : old.at().minus(taken).orNull();
        return at == null ? null : new Goal<>(rest, at);
    }

    /** {@code goal} with every position solved for put in terms of the rest. */
    private Goal<A> put(Goal<A> goal) {
        Map<A, ExactRatio> coefs = new LinkedHashMap<>(goal.coefs());
        ExactRatio constant = goal.constant();
        for (Solved<A> one : solved) {
            ExactRatio weight = coefs.remove(one.pivot());
            if (weight == null) {
                continue;
            }
            for (Map.Entry<A, ExactRatio> entry : walked(one.rest())) {
                ExactRatio moved = weight.times(entry.getValue()).orNull();
                ExactRatio had = coefs.getOrDefault(entry.getKey(), ExactRatio.ZERO);
                ExactRatio now = moved == null ? null : had.minus(moved).orNull();
                if (now == null) {
                    return null;
                }
                if (now.isZero()) {
                    coefs.remove(entry.getKey());
                } else {
                    coefs.put(entry.getKey(), now);
                }
            }
            ExactRatio taken = weight.times(one.at()).orNull();
            constant = taken == null ? null : constant.plus(taken).orNull();
            if (constant == null) {
                return null;
            }
        }
        return new Goal<>(coefs, constant);
    }

    /**
     * What {@code weights} weigh, in the one order the domain walks its positions in, with the
     * ones the goal names after the rest. An equality is solved for the last of its positions, so
     * the goal's are the ones put in terms of the others: the rules the goal is then asked
     * against are written in the positions the goal named, and still speak of the ones left.
     */
    private List<Map.Entry<A, ExactRatio>> walked(Map<A, ExactRatio> weights) {
        List<Map.Entry<A, ExactRatio>> out = new ArrayList<>();
        List<Map.Entry<A, ExactRatio>> named = new ArrayList<>();
        for (Map.Entry<A, ExactRatio> each : order.walking(weights.entrySet(), Map.Entry::getKey)) {
            (inTheGoal.contains(each.getKey()) ? named : out).add(each);
        }
        out.addAll(named);
        return out;
    }
}
