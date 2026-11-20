package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * The bounds on the input that together keep every run getting to a rule from stopping in what it
 * works out, where every stop is past where the representation of a number stops: one region of
 * the input, a bound for each place and side the stops ask one on. Within all of them no run stops
 * there.
 *
 * <p>How far out the region goes is a second fact, said of each bound apart: a bound is as far out
 * as one can be where a run with its place one step past it, every other bound of the region
 * holding, is shown to stop ({@code asFarOutAsCanBe}). That is a claim about the region, so it is
 * made once the region is whole and never of a bound alone.
 *
 * @param bounds          the bounds, each place and side once
 * @param asFarOutAsCanBe the bounds of {@code bounds} as far out as one can be
 */
public record WhatKeepsEveryRunGoing(List<ABoundThatKeepsEveryRunGoing> bounds,
                                     Set<ABoundThatKeepsEveryRunGoing> asFarOutAsCanBe) {

    public WhatKeepsEveryRunGoing {
        bounds = List.copyOf(bounds);
        asFarOutAsCanBe = Set.copyOf(asFarOutAsCanBe);
        for (int at = 0; at < bounds.size(); at++) {
            for (int other = at + 1; other < bounds.size(); other++) {
                if (bounds.get(at).onTheSameSideAs(bounds.get(other))) {
                    throw new IllegalArgumentException("a region bounds a place on a side once: "
                            + bounds);
                }
            }
        }
        if (!bounds.containsAll(asFarOutAsCanBe)) {
            throw new IllegalArgumentException("as far out as can be is said of a bound of the"
                    + " region: " + asFarOutAsCanBe);
        }
    }

    /**
     * What two readings of one rule say of the region, as one: the two together where each says
     * one ({@link #together}), and none where either says none — a run of that reading would be
     * one no bound said keeps going.
     */
    public static Optional<WhatKeepsEveryRunGoing> together(Optional<WhatKeepsEveryRunGoing> one,
                                                            Optional<WhatKeepsEveryRunGoing> other) {
        return one.isPresent() && other.isPresent()
                ? Optional.of(one.get().together(other.get())) : Optional.empty();
    }

    /** Whether {@code bound} is as far out as a bound of this region can be. */
    public boolean asFarOutAsCanBe(ABoundThatKeepsEveryRunGoing bound) {
        return asFarOutAsCanBe.contains(bound);
    }

    /**
     * The region that keeps the runs of both every run getting to one rule read twice: each place
     * and side bounded by the tighter of the two, so that a run within it is within each. How far
     * out each bound goes is shown of one region and not of the other's, so it stands only where
     * the two are one region; anywhere else nothing is said of it.
     */
    public WhatKeepsEveryRunGoing together(WhatKeepsEveryRunGoing other) {
        if (equals(other)) {
            return this;
        }
        if (bounds.equals(other.bounds)) {
            Set<ABoundThatKeepsEveryRunGoing> either = new LinkedHashSet<>(asFarOutAsCanBe);
            either.addAll(other.asFarOutAsCanBe);
            return new WhatKeepsEveryRunGoing(bounds, either);
        }
        List<ABoundThatKeepsEveryRunGoing> out = new ArrayList<>();
        for (ABoundThatKeepsEveryRunGoing each : bounds) {
            ABoundThatKeepsEveryRunGoing theirs = other.bounds.stream()
                    .filter(each::onTheSameSideAs).findFirst().orElse(null);
            out.add((theirs != null && theirs.within(each)) ? theirs : each);
        }
        for (ABoundThatKeepsEveryRunGoing theirs : other.bounds) {
            if (out.stream().noneMatch(theirs::onTheSameSideAs)) {
                out.add(theirs);
            }
        }
        return new WhatKeepsEveryRunGoing(out, Set.of());
    }
}
