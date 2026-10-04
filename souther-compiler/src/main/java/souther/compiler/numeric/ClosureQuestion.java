package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.HashMap;
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
        // Sorted by the order alone and not walked: a pair the order cannot tell apart is kept at
        // one place rather than refused, for the reason the class comment gives.
        List<A> sorted = new ArrayList<>(weighed);
        sorted.sort(order);
        Map<A, Integer> place = new HashMap<>();
        for (int at = 0; at < sorted.size(); at++) {
            A here = sorted.get(at);
            A before = at == 0 ? null : sorted.get(at - 1);
            place.put(here, before != null && order.compare(before, here) == 0
                    ? place.get(before) : at);
        }
        return new ClosureQuestion<>(List.copyOf(rules), Map.copyOf(spaced), Map.copyOf(place));
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
