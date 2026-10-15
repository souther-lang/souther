package souther.compiler.flow;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.UnaryOperator;

/**
 * What got a run down a path, in whatever words the naming has for it, whether they say all of it,
 * and what a run on it is seen doing.
 *
 * <p>Held apart, because each is a different question with its own readers. What holds on the way
 * is what a run read, which is what a reading of the positions read together takes. What a run is
 * seen doing is what proves a run took the way, which is what a reading steering a row or
 * crediting one takes — and the two part where a way is written down whole and a run on it looks
 * like a run on another: a truth the naming wrote at the arm it was seen at is seen there whichever
 * way into the arm a run came.
 *
 * @param path         the conditions along the way, as the naming writes them: what holds on
 *                     every run that took it
 * @param completeness whether the naming could write all of them
 * @param unworded     the truths on the way the naming had no words for, each once, with the way
 *                     it came out. Not everything a partial way is missing: what it was missing
 *                     besides is not carried, and a way that holds none of these may still be
 *                     partial. Empty on a complete one
 * @param seenAs       what a run on the way is seen doing, where that is less than {@code path}
 *                     says: the arm itself, for a way into an arm among others nothing a run is
 *                     seen doing tells it from. Null where it is {@code path}
 */
public record Provenance<P>(P path, Completeness completeness, List<UnwordedTruth> unworded,
                            P seenAs) {

    public Provenance {
        if (path == null) {
            throw new IllegalArgumentException("a path with nothing on it is still a path");
        }
        if (completeness == null) {
            throw new IllegalArgumentException("a path is either named whole or it is not: " + path);
        }
        unworded = List.copyOf(unworded);
        if (completeness == Completeness.COMPLETE && !unworded.isEmpty()) {
            throw new IllegalArgumentException("a way written whole has nothing unworded: " + path);
        }
    }

    /** What a run on the way is seen doing, which is what proves a run took it. */
    public P seen() {
        return seenAs == null ? path : seenAs;
    }

    /** Whether what a run is seen doing says all the way says. */
    public boolean isSeenWhole() {
        return seenAs == null;
    }

    /** The same path, with {@code truth} having come out {@code held} on the way to it where the
     *  naming had no words for it. */
    public Provenance<P> unworded(Core truth, boolean held) {
        List<UnwordedTruth> more = new ArrayList<>(unworded);
        more.add(new UnwordedTruth(truth, held));
        return new Provenance<>(path, Completeness.PARTIAL, more, seenAs);
    }

    /**
     * The way with no truth kept on it: what it is as a way. Two ways that differ only in a truth
     * they had no words for are one way, as they were before either was kept.
     */
    public Provenance<P> asAWay() {
        return unworded.isEmpty() ? this : new Provenance<>(path, completeness, List.of(), seenAs);
    }

    /** The same way, keeping only the truths {@code other} kept too: one way standing for runs on
     *  both knows of a truth only what both know. */
    public Provenance<P> sharedWith(Provenance<P> other) {
        if (unworded.equals(other.unworded)) {
            return this;
        }
        List<UnwordedTruth> both = new ArrayList<>(unworded);
        both.retainAll(Set.copyOf(other.unworded));
        return new Provenance<>(path, completeness, both, seenAs);
    }

    /**
     * The same way with what holds on it written again by {@code rewrite}, and what a run is seen
     * doing written again the same way; or null where either comes to no path.
     */
    public Provenance<P> rewritten(UnaryOperator<P> rewrite) {
        P now = rewrite.apply(path);
        if (now == null) {
            return null;
        }
        if (seenAs == null) {
            return new Provenance<>(now, completeness, unworded, null);
        }
        P seenNow = rewrite.apply(seenAs);
        return seenNow == null ? null : new Provenance<>(now, completeness, unworded, seenNow);
    }

    /**
     * A way on through this and then {@code after}: what holds on both, what a run on both is seen
     * doing, and whatever either had no words for — or null where the two settle one decision two
     * ways.
     */
    public Provenance<P> then(Provenance<P> after, Naming<P> naming) {
        P both = naming.join(path, after.path);
        if (both == null) {
            return null;
        }
        P seenBoth = null;
        if (seenAs != null || after.seenAs != null) {
            seenBoth = naming.join(seen(), after.seen());
            if (seenBoth == null) {
                return null;
            }
        }
        return new Provenance<>(both, completeness.and(after.completeness),
                truthsOfBoth(after), seenBoth);
    }

    private List<UnwordedTruth> truthsOfBoth(Provenance<P> after) {
        // Asked of every way under every arm, and almost every one of them has nothing unworded.
        if (after.unworded.isEmpty()) {
            return unworded;
        }
        if (unworded.isEmpty()) {
            return after.unworded;
        }
        Set<UnwordedTruth> both = new LinkedHashSet<>(unworded);
        both.addAll(after.unworded);
        return List.copyOf(both);
    }

    public boolean isComplete() {
        return completeness == Completeness.COMPLETE;
    }
}
