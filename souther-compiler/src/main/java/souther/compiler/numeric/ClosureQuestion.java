package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;

/**
 * Everything a closure of rules is worked out from, as one value.
 *
 * <p>A {@link ClosedState} is worked out from the rules, from how the values at each position they
 * weigh are spaced, and from the order those positions are walked in — and from nothing else. This
 * holds the three, and a closure is worked out from this and not from what it was made of
 * ({@link ClosedState#of(ClosureQuestion)}). So two of these that are equal are one closure: there
 * is no input the closure reads that this could have left out.
 *
 * <p><b>The rules in the order they are held.</b> What the rules leave does not depend on the order
 * they arrived in, and the closure says so. This does not lean on that: two orders of one set of
 * rules are two of these, which costs a second closure and never a wrong one.
 *
 * <p><b>The spacing of the positions the rules weigh, and of no others.</b> A spacing recorded for a
 * position no rule weighs is one the closure never asks about.
 *
 * <p><b>The order as what it says about those positions.</b> An order is a comparison, and two
 * comparisons that put the same positions in the same places are one order to every walk of them —
 * however they were written, and whether or not they are one object. So what is held is the place
 * each position has: how many of the others come before it. Two positions the order cannot tell
 * apart are at one place, and are handed to the closure that way, where a walk that meets them
 * together refuses them ({@link CanonicalOrder#walking}). They are not refused here: two such
 * positions in different rules are never walked together, and a refusal here would be one the
 * closure itself does not make.
 *
 * @param <A> what a position of the rules is
 */
final class ClosureQuestion<A> {

    private final List<AffineConstraint<A>> rules;
    private final Map<A, Granularity> spacing;
    private final Map<A, Integer> place;

    /** Worked out on the first asking. Comparing two of these walks every rule, and so would this. */
    private int hash;

    private ClosureQuestion(List<AffineConstraint<A>> rules, Map<A, Granularity> spacing,
                           Map<A, Integer> place) {
        this.rules = rules;
        this.spacing = spacing;
        this.place = place;
    }

    /**
     * The question {@code rules} put, spaced by {@code spacing} and walked in {@code order}.
     *
     * @throws IllegalStateException where a position a rule weighs has no spacing, which a domain
     *         holding the rules never lets happen — a rule is kept only once every position in it
     *         is spaced
     */
    static <A> ClosureQuestion<A> of(List<AffineConstraint<A>> rules,
                                     Function<A, Granularity> spacing, CanonicalOrder<A> order) {
        return of(rules, spacing, weighed -> placesIn(weighed, order));
    }

    /**
     * The same, with the places of the positions the rules weigh handed over by {@code placing}
     * rather than sorted out here — for a caller that has already put those positions in the same
     * order and kept what it came to.
     *
     * @param placing what {@link #placesIn} answers for the positions the rules weigh, under the
     *                order the closure is to walk them in
     */
    static <A> ClosureQuestion<A> of(List<AffineConstraint<A>> rules,
                                     Function<A, Granularity> spacing,
                                     Function<Set<A>, Map<A, Integer>> placing) {
        Set<A> weighed = new LinkedHashSet<>();
        rules.forEach(each -> weighed.addAll(each.form().coefs().keySet()));
        Map<A, Granularity> spaced = new HashMap<>();
        for (A position : weighed) {
            Granularity it = spacing.apply(position);
            if (it == null) {
                throw new IllegalStateException(
                        "a rule weighs `" + position + "`, and nothing says how it is spaced");
            }
            spaced.put(position, it);
        }
        return new ClosureQuestion<>(List.copyOf(rules), Map.copyOf(spaced),
                placing.apply(Collections.unmodifiableSet(weighed)));
    }

    /**
     * The questions {@code rules} put, one for each part of them that names no position another part
     * names.
     *
     * <p>Each of these is a closure on its own, and what the rules leave together is the product of
     * what these leave ({@link ClosedState#product}) — see {@link ClosedState} for why. So two sets
     * of rules that share a part share the question that part puts, whatever else each of them holds.
     *
     * @param placing as for {@link #of(List, Function, Function)}, asked once for each part
     */
    static <A> List<ClosureQuestion<A>> independent(List<AffineConstraint<A>> rules,
                                                    Function<A, Granularity> spacing,
                                                    Function<Set<A>, Map<A, Integer>> placing) {
        List<List<AffineConstraint<A>>> parts = independentRules(rules);
        List<ClosureQuestion<A>> out = new ArrayList<>(parts.size());
        for (List<AffineConstraint<A>> part : parts) {
            out.add(of(part, spacing, placing));
        }
        return out;
    }

    /**
     * {@code rules} parted where no position joins them: two rules are in one part where a chain of
     * rules, each weighing a position the next one weighs, runs from one to the other.
     *
     * <p>A rule is one edge over every position it weighs, so a sum over three positions holds all
     * three in one part. The parts come in the order of the first rule of each, and the rules of a
     * part in the order they were handed over, so the closure of a part reads its rules in the order
     * the closure of all of them would have.
     *
     * <p>No order of positions is asked for. Which parts there are is settled by which positions
     * each rule weighs, so it does not depend on the order a rule's positions are taken in — see
     * {@link #joining} — and asking an order to walk them would be a comparison made every time the
     * rules are asked, which is what keeping the places of a set of positions is there to save.
     */
    static <A> List<List<AffineConstraint<A>>> independentRules(List<AffineConstraint<A>> rules) {
        Map<A, Integer> firstNamedBy = new HashMap<>();
        int[] joinedTo = new int[rules.size()];
        for (int at = 0; at < rules.size(); at++) {
            joinedTo[at] = at;
            joining(rules.get(at), at, firstNamedBy, joinedTo);
        }
        Map<Integer, List<AffineConstraint<A>>> parts = new LinkedHashMap<>();
        for (int at = 0; at < rules.size(); at++) {
            parts.computeIfAbsent(rootOf(joinedTo, at), _ -> new ArrayList<>()).add(rules.get(at));
        }
        List<List<AffineConstraint<A>>> out = new ArrayList<>(parts.size());
        parts.values().forEach(part -> out.add(List.copyOf(part)));
        return out;
    }

    /**
     * The {@code at}-th rule joined to the part of every rule before it that weighs one of its
     * positions.
     *
     * <p>Its positions are taken as the form holds them. Each one joins two parts into one, and
     * which joins are made is the set of positions and not the order: joining is the union of two
     * sets, and two parts end up one exactly where some position is weighed by a rule of each,
     * whichever position was taken first.
     */
    private static <A> void joining(AffineConstraint<A> rule, int at, Map<A, Integer> firstNamedBy,
                                    int[] joinedTo) {
        for (A position : rule.form().coefs().keySet()) {
            Integer had = firstNamedBy.putIfAbsent(position, at);
            if (had != null) {
                int one = rootOf(joinedTo, had);
                int other = rootOf(joinedTo, at);
                joinedTo[Math.max(one, other)] = Math.min(one, other);
            }
        }
    }

    /** The first rule of the part {@code rule} has been joined to so far. */
    private static int rootOf(int[] joinedTo, int rule) {
        int at = rule;
        while (joinedTo[at] != at) {
            at = joinedTo[at];
        }
        return at;
    }

    /**
     * Where {@code order} puts each of {@code positions}: how many of the others come before it.
     *
     * <p>Sorted by the order alone and not walked: a pair the order cannot tell apart is kept at
     * one place rather than refused, for the reason the class comment gives. Settled by the order
     * and the positions and by nothing else, so what it comes to for one set of positions under one
     * order may be kept and handed back for the next question about the same positions.
     */
    static <A> Map<A, Integer> placesIn(Set<A> positions, CanonicalOrder<A> order) {
        List<A> sorted = new ArrayList<>(positions);
        sorted.sort(order);
        Map<A, Integer> place = new HashMap<>();
        for (int at = 0; at < sorted.size(); at++) {
            A here = sorted.get(at);
            A before = at == 0 ? null : sorted.get(at - 1);
            place.put(here, before != null && order.compare(before, here) == 0
                    ? place.get(before) : at);
        }
        return Map.copyOf(place);
    }

    /** The rules, in the order they are held. */
    List<AffineConstraint<A>> rules() {
        return rules;
    }

    /** How the values at a position the rules weigh are spaced. */
    Granularity spacingOf(A position) {
        return known(spacing.get(position), position);
    }

    /**
     * The order the positions are walked in, read off their places.
     *
     * <p>The same comparison as the order this was made with, over every position the rules weigh,
     * which are the only positions a closure of them walks. Asked about any other position it
     * refuses rather than guessing a place for it.
     */
    CanonicalOrder<A> order() {
        return (one, other) -> Integer.compare(known(place.get(one), one),
                known(place.get(other), other));
    }

    private static <T> T known(T answer, Object position) {
        if (answer == null) {
            throw new IllegalStateException(
                    "`" + position + "` is weighed by none of the rules being closed");
        }
        return answer;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof ClosureQuestion<?> it
                && hashCode() == it.hashCode()
                && place.equals(it.place)
                && spacing.equals(it.spacing)
                && rules.equals(it.rules);
    }

    @Override
    public int hashCode() {
        int had = hash;
        if (had == 0) {
            had = Objects.hash(rules, spacing, place);
            hash = had;
        }
        return had;
    }

    @Override
    public String toString() {
        return rules + " spaced " + spacing + " at " + place;
    }
}
