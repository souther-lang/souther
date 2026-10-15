package souther.compiler.flow;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What got a run down a path, in whatever words the naming has for it, and whether they say all of
 * it.
 *
 * <p>Two fields and not one, because the second is about the naming and the first is about the run.
 * A reading that steers rows takes both; a reading that asks what a value comes to takes neither.
 *
 * @param path         the conditions along the way, as the naming writes them
 * @param completeness whether the naming could write all of them
 * @param unworded     the truths on the way the naming had no words for, each once, with the way
 *                     it came out. Not everything a partial way is missing: what it was missing
 *                     besides is not carried, and a way that holds none of these may still be
 *                     partial. Empty on a complete one
 */
public record Provenance<P>(P path, Completeness completeness, List<UnwordedTruth> unworded) {

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

    /** The same path, with {@code truth} having come out {@code held} on the way to it where the
     *  naming had no words for it. */
    public Provenance<P> unworded(Core truth, boolean held) {
        List<UnwordedTruth> more = new ArrayList<>(unworded);
        more.add(new UnwordedTruth(truth, held));
        return new Provenance<>(path, Completeness.PARTIAL, more);
    }

    /**
     * The way with no truth kept on it: what it is as a way. Two ways that differ only in a truth
     * they had no words for are one way, as they were before either was kept.
     */
    public Provenance<P> asAWay() {
        return unworded.isEmpty() ? this : new Provenance<>(path, completeness, List.of());
    }

    /** The same way, keeping only the truths {@code other} kept too: one way standing for runs on
     *  both knows of a truth only what both know. */
    public Provenance<P> sharedWith(Provenance<P> other) {
        if (unworded.equals(other.unworded)) {
            return this;
        }
        List<UnwordedTruth> both = new ArrayList<>(unworded);
        both.retainAll(Set.copyOf(other.unworded));
        return new Provenance<>(path, completeness, both);
    }

    /** The same way written as {@code path}, missing what it was missing. */
    public Provenance<P> writtenAs(P path) {
        return new Provenance<>(path, completeness, unworded);
    }

    /**
     * What a way on to {@code path}, through this and then {@code after}, had no words for: whatever
     * either had none for.
     */
    public Provenance<P> then(P path, Provenance<P> after) {
        Completeness either = completeness.and(after.completeness);
        // Asked of every way under every arm, and almost every one of them has nothing unworded.
        if (after.unworded.isEmpty()) {
            return new Provenance<>(path, either, unworded);
        }
        if (unworded.isEmpty()) {
            return new Provenance<>(path, either, after.unworded);
        }
        Set<UnwordedTruth> both = new LinkedHashSet<>(unworded);
        both.addAll(after.unworded);
        return new Provenance<>(path, either, List.copyOf(both));
    }

    public boolean isComplete() {
        return completeness == Completeness.COMPLETE;
    }
}
