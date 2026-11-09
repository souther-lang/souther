package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The rules written over the positions their equalities leave free, so that a goal asked of them
 * is written the same way the rules are.
 *
 * <p>Each equality is solved for one of its positions, and a position solved for is put in terms of
 * the rest wherever it appears: in the other equalities, in every other rule, and in a goal. A
 * question that takes one rule as its premise ({@link FormReach}) finds in the rules so written what
 * it would have needed two to find. {@code x = a + b} beside {@code y = b + a} proves
 * {@code x - y} is nought.
 *
 * <p>Which position an equality is solved for is the one the rules use most, and among positions
 * they use alike, the last in the order the domain walks them ({@link Use}). Chosen by the names,
 * the rules written over what is left differ between two namings of one system, and what a question
 * finds in them with it. What the rules use of a position — how many name it, and in what shape of
 * rule — is the same under any naming and under any writing of a rule, so the names decide only
 * between positions nothing tells apart. The rules come out the same whichever order they were
 * said in, since each equality is solved for the position ranked last of those that none of the
 * others was already solved for.
 *
 * <p>What the reduced rules say is what the rules say, less. Every rule here follows from the
 * rules it was made of, and a goal written as {@link #put} writes it is equal to the goal wherever
 * the equalities hold, so what the reduced rules prove of the written goal the rules prove of the
 * goal. What is lost is what only the positions solved for carried — how their values are spaced,
 * where they stop — and that costs what is proved and never whether it is true. So this is asked
 * after the rules as they stand have not proved a goal, and in place of nothing.
 *
 * <p>Equalities that share no position are solved apart, each set of them as far as it can be. A
 * set the exact numbers cannot hold, that the equalities contradict, or whose solving takes more
 * than {@link #MOST_UPDATES} updates of a weight is left as the equalities it was and costs the
 * others nothing. A rule that cannot be written over the free positions is left out, which says
 * less and nothing false.
 */
final class ReducedRules<A> {

    /**
     * The most weights solving one set of equalities may update, counted as the work rather than
     * as the numbers it is done in: the exact numbers stop an arithmetic that cannot be held, and
     * this stops one that can be held and is too much to do.
     */
    static final int MOST_UPDATES = 20_000;

    /** A sum and a constant: {@code Σ coefs·position + constant}. */
    record Goal<A>(Map<A, ExactRatio> coefs, ExactRatio constant) {}

    /** A rule over the free positions: {@code Σ coefs·position + constant rel 0}. */
    record Rule<A>(Map<A, ExactRatio> coefs, ExactRatio constant, Rel rel) {}

    /** An equality solved for {@code pivot}: {@code pivot + Σ rest = at}. */
    private record Solved<A>(A pivot, Map<A, ExactRatio> rest, ExactRatio at) {}

    /**
     * How the rules use a position, written without its name: how many of them name it, and each
     * of those as the kind of rule, what the position weighs in it, how many positions it weighs
     * and what it is held to. A position is solved for in preference to one used less, and to one
     * used in other ways.
     *
     * <p>An equality and a hole are one rule written either way round ({@code x - 2y = 3} is
     * {@code -x + 2y = -3}), so what they weigh and are held to is counted by size: the use of a
     * position does not turn on which of the two writings the rules were given.
     */
    private record Use(int count, String ways) implements Comparable<Use> {

        @Override
        public int compareTo(Use other) {
            int byCount = Integer.compare(count, other.count);
            return byCount != 0 ? byCount : ways.compareTo(other.ways);
        }
    }

    private final CanonicalOrder<A> order;
    private final Map<A, Use> uses = new HashMap<>();
    private final List<Solved<A>> solved = new ArrayList<>();
    private final List<Rule<A>> rules = new ArrayList<>();
    /** Whether the updates of a weight are counted: while a set of equalities is solved. */
    private boolean metered;
    /** How many more weights this set of equalities may update. */
    private int left;

    private ReducedRules(CanonicalOrder<A> order) {
        this.order = order;
    }

    /**
     * {@code all} over the positions their equalities leave free, or null where there is nothing
     * to leave free: every equality is one the domain holds exactly already as a difference of two
     * positions, or none of the sets of equalities could be solved.
     */
    static <A> ReducedRules<A> of(List<AffineConstraint<A>> all, CanonicalOrder<A> order) {
        List<AffineConstraint.Equality<A>> equalities = new ArrayList<>();
        for (AffineConstraint<A> each : all) {
            if (each instanceof AffineConstraint.Equality<A> equality) {
                equalities.add(equality);
            }
        }
        if (equalities.stream().allMatch(each -> DifferenceBounds.holdsExactly(each, order))) {
            return null;
        }
        ReducedRules<A> reduced = new ReducedRules<>(order);
        reduced.uses.putAll(usesIn(all, order));
        List<AffineConstraint.Equality<A>> unsolved = new ArrayList<>();
        for (List<AffineConstraint.Equality<A>> set : apart(equalities, order)) {
            if (!reduced.solve(set)) {
                unsolved.addAll(set);
            }
        }
        reduced.metered = false;
        if (reduced.solved.isEmpty()) {
            return null;
        }
        for (AffineConstraint<A> each : all) {
            Rule<A> rule = switch (each) {
                case AffineConstraint.HalfSpace<A> half -> reduced.rewritten(
                        reduced.said(half.form()), half.bound().at(),
                        half.bound().inclusive() ? Rel.LE : Rel.LT);
                case AffineConstraint.Disequality<A> hole ->
                        reduced.rewritten(reduced.said(hole.form()), hole.at(), Rel.NE);
                // An equality that was solved is what the positions were solved from, and says
                // nothing more; one that was not is a rule as it was.
                case AffineConstraint.Equality<A> equality -> unsolved.contains(equality)
                        ? reduced.rewritten(reduced.said(equality.form()), equality.at(), Rel.EQ)
                        : null;
            };
            if (rule != null) {
                reduced.rules.add(rule);
            }
        }
        return reduced;
    }

    /**
     * {@code equalities} in the sets that share no position, each in the order it was given: the
     * positions an equality names are all one set, and so are those of any equality naming one of
     * them.
     */
    private static <A> List<List<AffineConstraint.Equality<A>>> apart(
            List<AffineConstraint.Equality<A>> equalities, CanonicalOrder<A> order) {
        Map<A, A> parent = new HashMap<>();
        for (AffineConstraint.Equality<A> each : equalities) {
            A first = null;
            for (A atom : each.form().atomsIn(order)) {
                parent.putIfAbsent(atom, atom);
                if (first == null) {
                    first = atom;
                } else {
                    parent.put(root(parent, atom), root(parent, first));
                }
            }
        }
        Map<A, List<AffineConstraint.Equality<A>>> sets = new LinkedHashMap<>();
        for (AffineConstraint.Equality<A> each : equalities) {
            A first = each.form().atomsIn(order).getFirst();
            sets.computeIfAbsent(root(parent, first), _ -> new ArrayList<>()).add(each);
        }
        return List.copyOf(sets.values());
    }

    private static <A> A root(Map<A, A> parent, A atom) {
        A at = atom;
        while (!parent.get(at).equals(at)) {
            at = parent.get(at);
        }
        return at;
    }

    /** How {@code all} use each position they name. */
    private static <A> Map<A, Use> usesIn(List<AffineConstraint<A>> all, CanonicalOrder<A> order) {
        Map<A, List<String>> ways = new HashMap<>();
        for (AffineConstraint<A> each : all) {
            // A bound has a side, which is what it says; a value has none to turn round.
            boolean sided = each instanceof AffineConstraint.HalfSpace<A>;
            String shape = switch (each) {
                case AffineConstraint.HalfSpace<A> half ->
                        (half.bound().inclusive() ? "<=" : "<") + half.bound().at();
                case AffineConstraint.Equality<A> equality -> "=" + equality.at().abs();
                case AffineConstraint.Disequality<A> hole -> "/=" + hole.at().abs();
            };
            int named = each.form().atomsIn(order).size();
            for (Map.Entry<A, ExactRatio> entry : each.form().entriesIn(order)) {
                ExactRatio weight = sided ? entry.getValue() : entry.getValue().abs();
                ways.computeIfAbsent(entry.getKey(), _ -> new ArrayList<>())
                        .add(shape + ";" + weight + ";" + named);
            }
        }
        Map<A, Use> out = new HashMap<>();
        ways.forEach((atom, each) -> {
            Collections.sort(each);
            out.put(atom, new Use(each.size(), String.join("|", each)));
        });
        return out;
    }

    /** The rules over the free positions. */
    List<Rule<A>> rules() {
        return rules;
    }

    /** {@code goal} over the free positions, or null where the arithmetic could not hold it. */
    Goal<A> put(Goal<A> goal) {
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
                ExactRatio now = moved == null || spent() ? null : had.minus(moved).orNull();
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

    /** Whether the weight about to be updated is one too many for the set of equalities being
     *  solved. */
    private boolean spent() {
        return metered && --left < 0;
    }

    /** {@code Σ coefs rel at} over the free positions, or null where the arithmetic could not
     *  hold it. */
    private Rule<A> rewritten(Map<A, ExactRatio> coefs, ExactRatio at, Rel rel) {
        Goal<A> put = put(new Goal<>(coefs, at.negated()));
        if (put == null) {
            return null;
        }
        // A value held or held away from has no side to turn round, so it is written the one way:
        // the position ranked first weighs more than nought.
        boolean turned = (rel == Rel.EQ || rel == Rel.NE) && !put.coefs().isEmpty()
                && walked(put.coefs()).getFirst().getValue().signum() < 0;
        return turned
                ? new Rule<>(negated(put.coefs()), put.constant().negated(), rel)
                : new Rule<>(put.coefs(), put.constant(), rel);
    }

    private static <A> Map<A, ExactRatio> negated(Map<A, ExactRatio> coefs) {
        Map<A, ExactRatio> out = new LinkedHashMap<>();
        coefs.forEach((position, weight) -> out.put(position, weight.negated()));
        return out;
    }

    /**
     * Solves {@code set} for one position each, within {@link #MOST_UPDATES} updates — or leaves
     * what was solved as it was and answers false, where one cannot be held, the set contradicts
     * itself, or the work is more than that.
     */
    private boolean solve(List<AffineConstraint.Equality<A>> set) {
        List<Solved<A>> before = new ArrayList<>(solved);
        metered = true;
        left = MOST_UPDATES;
        for (AffineConstraint.Equality<A> each : set) {
            if (!take(each)) {
                solved.clear();
                solved.addAll(before);
                return false;
            }
        }
        return true;
    }

    /** Solves {@code equality} for one position, after putting the ones already solved in terms of
     *  the rest. False where the arithmetic could not hold it, or it says something no value
     *  satisfies. */
    private boolean take(AffineConstraint.Equality<A> equality) {
        Goal<A> as = put(new Goal<>(said(equality.form()), equality.at().negated()));
        if (as == null) {
            return false;
        }
        List<Map.Entry<A, ExactRatio>> walked = walked(as.coefs());
        if (walked.isEmpty()) {
            // Said already, or said against itself.
            return as.constant().isZero();
        }
        Map.Entry<A, ExactRatio> last = walked.getLast();
        A pivot = last.getKey();
        Map<A, ExactRatio> rest = new LinkedHashMap<>();
        for (Map.Entry<A, ExactRatio> entry : walked) {
            if (!entry.getKey().equals(pivot)) {
                ExactRatio scaled = spent() ? null
                        : entry.getValue().dividedBy(last.getValue()).orNull();
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

    /** What {@code form} weighs, in the one order the domain walks its positions in. */
    private Map<A, ExactRatio> said(CanonicalForm<A> form) {
        Map<A, ExactRatio> said = new LinkedHashMap<>();
        for (Map.Entry<A, ExactRatio> each : form.entriesIn(order)) {
            said.put(each.getKey(), each.getValue());
        }
        return said;
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
            ExactRatio now = moved == null || spent() ? null : had.minus(moved).orNull();
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

    /**
     * What {@code weights} weigh, the positions solved for first-last: ranked by how the rules use
     * them, and among those used alike in the order the domain walks them. The last is the one an
     * equality is solved for.
     */
    private List<Map.Entry<A, ExactRatio>> walked(Map<A, ExactRatio> weights) {
        List<Map.Entry<A, ExactRatio>> ranked =
                new ArrayList<>(order.walking(weights.entrySet(), Map.Entry::getKey));
        ranked.sort(Comparator.comparing(each -> uses.get(each.getKey())));
        return ranked;
    }
}
