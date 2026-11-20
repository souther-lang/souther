package souther.compiler.inputs;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The declarations that together keep every run getting to a rule from taking a number past where
 * its type stops in what the rule works out: one region of the input, as the invariants an author
 * declares make it. Within all of them no run stops so there. A stop of any other kind, such as a
 * construction on the way refusing what it is handed, is none of what this keeps a run from.
 *
 * <p>Said of what the invariants are declared on, and not of the places of the input: a data's
 * invariant holds every value of it, so two places one data holds are bounded by one declaration,
 * the tighter of what each asks, and the region is the declarations whatever order they were met
 * in. Made only where each data keeps a value under them: what its rules already leave it, met
 * with both sides declared, holds a whole number, every one of which is a value.
 *
 * <p>How far out the region goes is a second fact, said of each bound apart: a bound is as far out
 * as one can be where a run with it declared one step further out, every other declaration
 * holding, is shown to stop ({@code asFarOutAsCanBe}). That is a claim about the region, so it is
 * made once the region is whole and never of a bound alone.
 *
 * @param bounds          the declarations, each data and side once
 * @param asFarOutAsCanBe the bounds of {@code bounds} as far out as one can be
 */
public record WhatKeepsEveryRunGoing(Set<ABoundThatKeepsEveryRunGoing> bounds,
                                     Set<ABoundThatKeepsEveryRunGoing> asFarOutAsCanBe) {

    public WhatKeepsEveryRunGoing {
        bounds = Collections.unmodifiableSequencedSet(new LinkedHashSet<>(bounds));
        asFarOutAsCanBe = Set.copyOf(asFarOutAsCanBe);
        if (bounds.stream().map(ABoundThatKeepsEveryRunGoing::side).distinct().count()
                != bounds.size() || !keepsEveryDataAValue(bounds)) {
            throw new IllegalArgumentException("a region declares each data and side once, and"
                    + " leaves each a value: " + bounds);
        }
        if (!bounds.containsAll(asFarOutAsCanBe)) {
            throw new IllegalArgumentException("as far out as can be is said of a bound of the"
                    + " region: " + asFarOutAsCanBe);
        }
    }

    /**
     * The region {@code asked} declare, each data and side bounded by the tightest of them, with
     * nothing yet said of how far out — or none where that leaves some data no value.
     */
    public static Optional<WhatKeepsEveryRunGoing> of(
            Collection<ABoundThatKeepsEveryRunGoing> asked) {
        Map<ABoundThatKeepsEveryRunGoing.Side, ABoundThatKeepsEveryRunGoing> tightest =
                new LinkedHashMap<>();
        for (ABoundThatKeepsEveryRunGoing each : asked) {
            tightest.merge(each.side(), each, (one, other) -> one.within(other) ? one : other);
        }
        return keepsEveryDataAValue(tightest.values())
                ? Optional.of(new WhatKeepsEveryRunGoing(new LinkedHashSet<>(tightest.values()),
                        Set.of()))
                : Optional.empty();
    }

    /** The same region, with {@code farOut}, bounds of it, said as far out as each can be. */
    public WhatKeepsEveryRunGoing asFarOutAsCanBe(Set<ABoundThatKeepsEveryRunGoing> farOut) {
        return new WhatKeepsEveryRunGoing(bounds, farOut);
    }

    /**
     * What two readings of one rule say of the region, as one: the declarations of both, each data
     * and side bounded by the tighter, so that a run within it is within each — and none where
     * either says none, a run of that reading being one no declaration said keeps going, or where
     * the two together leave some data no value. How far out a bound goes is shown of one region,
     * and stands only where the two together are that region, whatever order either met its
     * declarations in.
     */
    public static Optional<WhatKeepsEveryRunGoing> together(Optional<WhatKeepsEveryRunGoing> one,
                                                            Optional<WhatKeepsEveryRunGoing> other) {
        if (one.isEmpty() || other.isEmpty()) {
            return Optional.empty();
        }
        Set<ABoundThatKeepsEveryRunGoing> both = new LinkedHashSet<>(one.get().bounds);
        both.addAll(other.get().bounds);
        return of(both).map(region -> {
            Set<ABoundThatKeepsEveryRunGoing> farOut = new LinkedHashSet<>();
            for (WhatKeepsEveryRunGoing each : List.of(one.get(), other.get())) {
                if (each.bounds.equals(region.bounds)) {
                    farOut.addAll(each.asFarOutAsCanBe);
                }
            }
            return region.asFarOutAsCanBe(farOut);
        });
    }

    /** Whether {@code bound} is as far out as a bound of this region can be. */
    public boolean asFarOutAsCanBe(ABoundThatKeepsEveryRunGoing bound) {
        return asFarOutAsCanBe.contains(bound);
    }

    /** Whether every data {@code bounds} declare on keeps a whole number under them, within what
     *  its rules already leave it, every one of which is a value. */
    private static boolean keepsEveryDataAValue(
            Collection<ABoundThatKeepsEveryRunGoing> bounds) {
        Map<ABoundThatKeepsEveryRunGoing.Holder, BigInteger[]> left = new LinkedHashMap<>();
        for (ABoundThatKeepsEveryRunGoing each : bounds) {
            BigInteger[] ends = left.computeIfAbsent(each.holder(),
                    _ -> new BigInteger[] {each.held().least(), each.held().greatest()});
            ends[0] = tighter(ends[0], each.held().least(), true);
            ends[1] = tighter(ends[1], each.held().greatest(), false);
            ends[each.atMost() ? 1 : 0] = tighter(ends[each.atMost() ? 1 : 0], each.at(),
                    !each.atMost());
        }
        return left.values().stream().allMatch(ends -> ends[0] == null || ends[1] == null
                || ends[0].compareTo(ends[1]) <= 0);
    }

    /** The tighter of two ends of one side, a least where {@code least}: either where the other
     *  is none. */
    private static BigInteger tighter(BigInteger one, BigInteger other, boolean least) {
        if (one == null || other == null) {
            return one == null ? other : one;
        }
        return least ? one.max(other) : one.min(other);
    }
}
