package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.ToIntFunction;

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

    /**
     * The order {@link #place} was read off. Carried and not part of what this question is: two
     * orders that put the positions in the same places put one question, which {@link #equals}
     * says by the places. What it is for is {@link #isPutBy}, where the order the places came from
     * is the order being asked about, and the places need not be read again.
     */
    private final CanonicalOrder<A> placedBy;

    /** Worked out on the first asking. Comparing two of these walks every rule, and so would this. */
    private int hash;

    /** The positions in the order, for a question that follows this one; null until asked for. */
    private volatile List<A> sorted;

    private ClosureQuestion(List<AffineConstraint<A>> rules, Map<A, Granularity> spacing,
                           Map<A, Integer> place, CanonicalOrder<A> placedBy) {
        this.rules = rules;
        this.spacing = spacing;
        this.place = place;
        this.placedBy = placedBy;
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
        return of(rules, spacing, order, weighed -> placesIn(weighed, order));
    }

    /**
     * The same, with the places of the positions the rules weigh handed over by {@code placing}
     * rather than sorted out here — for a caller that has already put those positions in the same
     * order and kept what it came to.
     *
     * @param placing what {@link #placesIn} answers for the positions the rules weigh under
     *                {@code order}
     */
    static <A> ClosureQuestion<A> of(List<AffineConstraint<A>> rules,
                                     Function<A, Granularity> spacing, CanonicalOrder<A> order,
                                     Function<Set<A>, Map<A, Integer>> placing) {
        Set<A> weighed = new LinkedHashSet<>();
        rules.forEach(each -> weighed.addAll(each.form().coefs().keySet()));
        return stated(rules, weighed, spacing, order, placing);
    }

    /**
     * The question {@code rules} put, which are the very rules of {@code before} followed by others,
     * with the positions of {@code before} taken as they are and only the rules after them read for
     * what they weigh; the question {@link #of} puts for the same rules where they are not.
     */
    static <A> ClosureQuestion<A> following(ClosureQuestion<A> before,
                                            List<AffineConstraint<A>> rules,
                                            Function<A, Granularity> spacing,
                                            CanonicalOrder<A> order,
                                            Function<Set<A>, Map<A, Integer>> placing) {
        int had = before == null ? 0 : before.rules.size();
        if (before == null || rules.size() <= had) {
            return of(rules, spacing, order, placing);
        }
        for (int at = 0; at < had; at++) {
            if (rules.get(at) != before.rules.get(at)) {
                return of(rules, spacing, order, placing);
            }
        }
        Set<A> weighed = new LinkedHashSet<>(before.place.keySet());
        rules.subList(had, rules.size()).forEach(each -> weighed.addAll(each.form().coefs().keySet()));
        Placed<A> placed = placedFrom(before, weighed, order);
        if (placed == null) {
            return stated(rules, weighed, spacing, order, placing);
        }
        ClosureQuestion<A> out = stated(rules, weighed, spacing, order, _ -> placed.place());
        out.sorted = placed.sorted();
        return out;
    }

    /** Where each position is, and the positions in the order they are. */
    private record Placed<A>(Map<A, Integer> place, List<A> sorted) {}

    /**
     * Where {@code order} puts each of {@code weighed}, which are the positions of {@code before} and
     * some more, worked out from where it put the ones before: only a position that was not there is
     * compared, with as many of the others as it takes to find where it goes — and not every
     * position with the ones near it, which is what {@link #placesIn} does for the positions of
     * a question that has none to follow. Null where {@code before} was placed by another order.
     *
     * <p>The places are the ones {@link #placesIn} gives: how many of the others come before a
     * position, two that the order cannot tell apart sharing one. Two positions that were next to
     * one another before and are still are told apart as they were.
     */
    private static <A> Placed<A> placedFrom(ClosureQuestion<A> before, Set<A> weighed,
                                           CanonicalOrder<A> order) {
        if (before.placedBy != order) {
            return null;
        }
        List<A> added = new ArrayList<>();
        for (A position : weighed) {
            if (!before.place.containsKey(position)) {
                added.add(position);
            }
        }
        if (before.place.size() + added.size() != weighed.size()) {
            return null;
        }
        List<A> merged = new ArrayList<>(before.positionsInOrder());
        added.sort(order);
        for (A position : added) {
            int low = 0;
            int high = merged.size();
            while (low < high) {
                int middle = (low + high) >>> 1;
                if (order.compare(position, merged.get(middle)) < 0) {
                    high = middle;
                } else {
                    low = middle + 1;
                }
            }
            merged.add(low, position);
        }
        Map<A, Integer> place = HashMap.newHashMap(merged.size());
        for (int at = 0; at < merged.size(); at++) {
            A here = merged.get(at);
            int number = at;
            if (at > 0) {
                A previous = merged.get(at - 1);
                boolean together = before.place.containsKey(here) && before.place.containsKey(previous)
                        ? before.place.get(previous).equals(before.place.get(here))
                        : order.compare(previous, here) == 0;
                if (together) {
                    number = place.get(previous);
                }
            }
            place.put(here, number);
        }
        return new Placed<>(Map.copyOf(place), merged);
    }

    /** The positions in the order, the ones it cannot tell apart next to one another. */
    private List<A> positionsInOrder() {
        List<A> held = sorted;
        if (held == null) {
            held = new ArrayList<>(place.keySet());
            held.sort(Comparator.comparingInt(place::get));
            sorted = held;
        }
        return held;
    }

    private static <A> ClosureQuestion<A> stated(List<AffineConstraint<A>> rules, Set<A> weighed,
                                                 Function<A, Granularity> spacing,
                                                 CanonicalOrder<A> order,
                                                 Function<Set<A>, Map<A, Integer>> placing) {
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
                placing.apply(Collections.unmodifiableSet(weighed)), order);
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

    /**
     * Where each position the rules weigh stands in the order they are walked in: the places this
     * question was stated with, which a reader of forms over these positions is handed rather than
     * working them out again.
     */
    Map<A, Integer> places() {
        return place;
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
        return new CanonicalOrder<>() {
            @Override
            public int compare(A one, A other) {
                return Integer.compare(ClosureQuestion.this.placeOf(one),
                        ClosureQuestion.this.placeOf(other));
            }

            /** The places themselves, which are what this order is. */
            @Override
            public ToIntFunction<A> placeOf() {
                return ClosureQuestion.this::placeOf;
            }

            /**
             * The same comparison as {@code placedBy} over every position a form of these rules
             * names, so the walk of such a form is the one {@code placedBy} keeps. A form that names
             * a position none of the rules weighs is walked here, and refused, whatever was kept.
             */
            @Override
            public List<Map.Entry<A, ExactRatio>> walkOf(
                    CanonicalForm<A> form, Supplier<List<Map.Entry<A, ExactRatio>>> walk) {
                return form.namesOnly(place.keySet()) ? placedBy.walkOf(form, walk) : walk.get();
            }
        };
    }

    /** Where {@code position} stands among the positions the rules weigh. */
    private int placeOf(A position) {
        return known(place.get(position), position);
    }

    private static <T> T known(T answer, Object position) {
        if (answer == null) {
            throw new IllegalStateException(
                    "`" + position + "` is weighed by none of the rules being closed");
        }
        return answer;
    }

    /**
     * Whether the rules this holds, spaced by {@code spacing} and walked in {@code order}, put this
     * question — the three things {@link #equals} compares, asked of rules already known to be
     * these, so that nothing has to be built to ask it.
     *
     * <p>Here and not with whoever lends a closure, because what a closure is worked out from is
     * this class's to say: a fourth thing added to it is a fourth thing this asks.
     *
     * @param placing what {@link #placesIn} answers under {@code order}, asked only where
     *                {@code order} is not the one these places were read off
     */
    boolean isPutBy(Function<A, Granularity> spacing, CanonicalOrder<A> order,
                    Function<Set<A>, Map<A, Integer>> placing) {
        for (Map.Entry<A, Granularity> each : this.spacing.entrySet()) {
            if (!each.getValue().equals(spacing.apply(each.getKey()))) {
                return false;
            }
        }
        return order == placedBy || place.equals(placing.apply(this.spacing.keySet()));
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
