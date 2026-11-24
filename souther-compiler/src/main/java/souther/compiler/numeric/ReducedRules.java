package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
 * <p>An equality is solved for a position the rules use most ({@link Use}), and there is one
 * reduction for each way of choosing among the positions they use alike. Chosen by the names, the
 * rules written over what is left differ between two namings of one system, and what a question
 * finds in them with it. What the rules use of a position — how many name it, and in what shape of
 * rule — is the same under any naming and under any writing of a rule, so the choices are the same
 * under any naming, and what is proved by any of them is proved under every naming. More than
 * {@link #MOST_CHOICES} of them are none, since the first few would be the names' choice.
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

    /**
     * The most reductions the rules may have, one for each way of choosing among the positions
     * they use alike. Past it none is used, and not the first few in the order of the names: which
     * ones those were would be the names deciding again.
     */
    static final int MOST_CHOICES = 16;

    /**
     * The most ways of choosing that are tried to find the reductions, before they are counted
     * as one for each set of positions solved for. More than that is more than {@link
     * #MOST_CHOICES} reductions for the purpose of this bound.
     */
    static final int MOST_WAYS = 256;

    /**
     * The most equalities of one set the ways of choosing are looked for among. Finding them is a descent one
     * level for each equality, so this bounds how deep it goes as well as how wide: equalities that
     * add nothing — each a combination of the others — take a level and no choice, and the ways
     * counted above would not stop them. Past it no reduction is used, for every naming alike. What
     * the equalities come to together is read without any descent ({@link EqualitySpan}).
     */
    static final int MOST_EQUATIONS = 64;

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

    private static final Use UNUSED = new Use(0, "");

    private final CanonicalOrder<A> order;
    private final Map<A, Use> uses;
    private final List<Solved<A>> solved;
    private final List<Rule<A>> rules;
    /** Whether the updates of a weight are counted: while a set of equalities is solved. */
    private boolean metered;
    /** How many more weights this set of equalities may update. */
    private int left;
    /** How many weights a set of equalities may update in all, one way of solving it at a time. */
    private int mostUpdates = MOST_UPDATES;

    /** A reduction being made, whose equalities are solved as it goes. */
    private ReducedRules(CanonicalOrder<A> order, Map<A, Use> uses) {
        this(order, uses, new ArrayList<>());
    }

    private ReducedRules(CanonicalOrder<A> order, Map<A, Use> uses, List<Solved<A>> solved) {
        this(order, uses, solved, List.of());
    }

    private ReducedRules(CanonicalOrder<A> order, Map<A, Use> uses, List<Solved<A>> solved,
                         List<Rule<A>> rules) {
        this.order = order;
        this.uses = uses;
        this.solved = solved;
        this.rules = rules;
    }

    /**
     * One way a set of equalities is solved: the positions solved for, or the equalities left as
     * they were where the set could not be solved.
     */
    private record Choice<A>(List<Solved<A>> solved, List<AffineConstraint.Equality<A>> unsolved) {

        /** What tells two ways apart: the same positions solved for are the same reduction. */
        Map.Entry<Set<Solved<A>>, List<AffineConstraint.Equality<A>>> identity() {
            return Map.entry(Set.copyOf(solved), unsolved);
        }
    }

    /**
     * {@code all} over the positions their equalities leave free, one reduction for each way of
     * choosing among the positions the rules use alike, or none where there is nothing to leave
     * free: every equality is one the domain holds exactly already as a difference of two
     * positions, none of the sets of equalities could be solved, or the ways of choosing are more
     * than {@link #MOST_CHOICES}. A set of more equalities than {@link #MOST_EQUATIONS} is left as
     * the equalities it was.
     */
    static <A> List<ReducedRules<A>> of(List<AffineConstraint<A>> all, CanonicalOrder<A> order) {
        return of(all, order, MOST_UPDATES);
    }

    /** The same, with the updates of a weight a way of solving a set of equalities may spend
     *  said. */
    static <A> List<ReducedRules<A>> of(List<AffineConstraint<A>> all, CanonicalOrder<A> order,
                                        int mostUpdates) {
        List<AffineConstraint.Equality<A>> equalities = new ArrayList<>();
        for (AffineConstraint<A> each : all) {
            if (each instanceof AffineConstraint.Equality<A> equality) {
                equalities.add(equality);
            }
        }
        if (equalities.stream().allMatch(each -> DifferenceBounds.holdsExactly(each, order))) {
            return List.of();
        }
        ReducedRules<A> scratch = new ReducedRules<>(order, usesIn(all, order));
        scratch.mostUpdates = mostUpdates;
        List<Choice<A>> together = List.of(new Choice<>(List.of(), List.of()));
        for (List<AffineConstraint.Equality<A>> set : apart(equalities, order)) {
            List<Choice<A>> choices = scratch.choicesFor(set);
            if (choices == null || together.size() * choices.size() > MOST_CHOICES) {
                return List.of();
            }
            List<Choice<A>> crossed = new ArrayList<>();
            for (Choice<A> before : together) {
                for (Choice<A> choice : choices) {
                    crossed.add(new Choice<>(joined(before.solved(), choice.solved()),
                            joined(before.unsolved(), choice.unsolved())));
                }
            }
            together = crossed;
        }
        List<ReducedRules<A>> out = new ArrayList<>();
        for (Choice<A> each : together) {
            if (!each.solved().isEmpty()) {
                out.add(scratch.written(all, each));
            }
        }
        return out;
    }

    private static <T> List<T> joined(List<T> first, List<T> second) {
        List<T> out = new ArrayList<>(first);
        out.addAll(second);
        return out;
    }

    /** The rules written over what {@code choice} leaves free. */
    private ReducedRules<A> written(List<AffineConstraint<A>> all, Choice<A> choice) {
        // Worked out over a copy that is still being made, and handed on only once it is finished:
        // what is handed on is read by whoever holds it and is never changed.
        ReducedRules<A> reduced = new ReducedRules<>(order, uses, new ArrayList<>(choice.solved()));
        List<Rule<A>> written = new ArrayList<>();
        List<AffineConstraint.Equality<A>> unsolved = choice.unsolved();
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
                written.add(rule);
            }
        }
        return new ReducedRules<>(order, uses, List.copyOf(reduced.solved), List.copyOf(written));
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

    /** {@code form + constant}, as a goal to put over the free positions. */
    Goal<A> goalOf(CanonicalForm<A> form, ExactRatio constant) {
        return new Goal<>(said(form), constant);
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
            if (!spends(one.rest().size())) {
                return null;
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
     * Whether {@code weights} more weights may be updated for the set of equalities being solved,
     * which they are charged for before any is, and not as each is done. What a step costs is how
     * many weights it names, whether or not the numbers go on being held: counted as they are
     * updated, a step that failed part of the way would have cost the weights done before it, which
     * is the order the positions are walked in and so the names'.
     */
    private boolean spends(int weights) {
        if (!metered) {
            return true;
        }
        left -= weights;
        return left >= 0;
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
     * Every way {@code set} is solved for one position each, within {@link #MOST_UPDATES} updates
     * a way: an equality is solved for each of the positions the rules use most and alike, and the
     * ways that solve for the same positions are one. A way that cannot be taken to its end, where
     * a weight cannot be held, the set contradicts itself, or the work is more than that, leaves the
     * set as the equalities it was. Null where the ways are more than {@link #MOST_CHOICES} or
     * {@link #MOST_WAYS} are tried to find them.
     */
    private List<Choice<A>> choicesFor(List<AffineConstraint.Equality<A>> set) {
        if (set.size() > MOST_EQUATIONS) {
            return List.of(new Choice<>(List.of(), set));
        }
        solved.clear();
        metered = true;
        left = mostUpdates;
        Map<Map.Entry<Set<Solved<A>>, List<AffineConstraint.Equality<A>>>, Choice<A>> found =
                new LinkedHashMap<>();
        boolean within = descend(set, 0, found, new int[1]);
        metered = false;
        solved.clear();
        return within ? List.copyOf(found.values()) : null;
    }

    /** Takes {@code set} from {@code index} on, in every way the choice of a position allows. False
     *  where the ways are too many. */
    private boolean descend(List<AffineConstraint.Equality<A>> set, int index,
                            Map<Map.Entry<Set<Solved<A>>, List<AffineConstraint.Equality<A>>>,
                                    Choice<A>> found, int[] ways) {
        if (index == set.size()) {
            Choice<A> done = new Choice<>(new ArrayList<>(solved), List.of());
            found.putIfAbsent(done.identity(), done);
            return ++ways[0] <= MOST_WAYS && found.size() <= MOST_CHOICES;
        }
        AffineConstraint.Equality<A> equality = set.get(index);
        Goal<A> as = put(new Goal<>(said(equality.form()), equality.at().negated()));
        List<Map.Entry<A, ExactRatio>> walked = as == null ? List.of() : walked(as.coefs());
        List<Solved<A>> before = new ArrayList<>(solved);
        int updates = left;
        boolean within = true;
        if (as != null && walked.isEmpty() && as.constant().isZero()) {
            // Said already.
            return descend(set, index + 1, found, ways);
        }
        if (as != null && !walked.isEmpty()) {
            Use last = useOf(walked.getLast().getKey());
            for (Map.Entry<A, ExactRatio> pivot : walked) {
                if (useOf(pivot.getKey()).compareTo(last) != 0) {
                    continue;
                }
                if (take(as, walked, pivot)) {
                    within = descend(set, index + 1, found, ways);
                } else {
                    within = unsolved(set, found, ways);
                }
                solved.clear();
                solved.addAll(before);
                left = updates;
                if (!within) {
                    return false;
                }
            }
            return true;
        }
        // Said against itself, or in weights that cannot be held.
        return unsolved(set, found, ways);
    }

    /** Records that {@code set} was left as the equalities it was, on the way being tried. */
    private boolean unsolved(List<AffineConstraint.Equality<A>> set,
                             Map<Map.Entry<Set<Solved<A>>, List<AffineConstraint.Equality<A>>>,
                                     Choice<A>> found, int[] ways) {
        Choice<A> asItWas = new Choice<>(List.of(), set);
        found.putIfAbsent(asItWas.identity(), asItWas);
        return ++ways[0] <= MOST_WAYS && found.size() <= MOST_CHOICES;
    }

    /** Solves {@code as} for {@code last}, which is one of the {@code walked}, after putting the
     *  ones already solved in terms of the rest. False where the arithmetic could not hold it. */
    private boolean take(Goal<A> as, List<Map.Entry<A, ExactRatio>> walked,
                         Map.Entry<A, ExactRatio> last) {
        A pivot = last.getKey();
        Map<A, ExactRatio> rest = new LinkedHashMap<>();
        if (!spends(walked.size())) {
            return false;
        }
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
        if (!spends(fresh.rest().size())) {
            return null;
        }
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

    /**
     * What {@code weights} weigh, the positions solved for first-last: ranked by how the rules use
     * them, and among those used alike in the order the domain walks them. The last is the one an
     * equality is solved for.
     */
    private List<Map.Entry<A, ExactRatio>> walked(Map<A, ExactRatio> weights) {
        List<Map.Entry<A, ExactRatio>> ranked =
                new ArrayList<>(order.walking(weights.entrySet(), Map.Entry::getKey));
        ranked.sort(Comparator.comparing(each -> useOf(each.getKey())));
        return ranked;
    }

    /** How the rules use {@code position}; a position none was ranked for is used as nothing. */
    private Use useOf(A position) {
        return uses.getOrDefault(position, UNUSED);
    }
}
