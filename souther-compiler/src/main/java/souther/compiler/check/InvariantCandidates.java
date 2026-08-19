package souther.compiler.check;

import souther.compiler.numeric.NumericDomain.Bounds;

import java.util.ArrayList;
import java.util.List;

/**
 * Ranges worth asking whether a reduction stays inside.
 *
 * <p>Guesses, and nothing here is sound or is meant to be. What makes a range an answer is
 * {@link InductiveBounds} proving the seed lies in it and the step never leaves it; this only says
 * which ranges are worth putting through that. A guess that is wrong costs a check and is thrown
 * away, so the list may be as incomplete as it likes and may be lengthened without anything about
 * soundness being reconsidered — which is the whole reason it is not written inside the proof.
 *
 * <p>Every guess is made from the seed. That is not an accident of this list: a reduction's answer is
 * the seed where the container is empty, so a range the seed is outside is refused before the step is
 * read at all, and a generator proposing one would be proposing something that cannot be proved.
 *
 * <p>What is not here is a range read off what the answer is used for. Guessing {@code [0, +∞)}
 * because a construction wants it would make what is proved of a value depend on what is asked of it,
 * and the same fold would answer differently at two call sites.
 */
final class InvariantCandidates {

    private InvariantCandidates() {}

    /**
     * The ranges to try, given what the seed lies between and what the step answers with nothing
     * assumed about the accumulator.
     *
     * <p>Four, and each is a different thing a fold does. The seed itself is what a step preserving
     * its accumulator answers. Open above the seed and open below it are the two directions an
     * accumulation runs, and they are the case an author writes: a total starting at zero that only
     * grows. The seed joined with the step is for a step that does not read the accumulator at all,
     * where the answer is the seed or is whatever the step answered, and the join is already the
     * whole of it.
     *
     * <p>The fourth is proposed whether or not the step reads the accumulator, and no reading decides
     * that here. Where it does read it, {@code stepWithNothingAssumed} is unbounded — the accumulator
     * is an atom the domain holds nothing about — so the join is unbounded too and proves nothing. A
     * test of the step's shape would answer the same and would be a second place that decides what a
     * step does with what it was handed.
     */
    static List<Bounds> from(Bounds seed, Bounds stepWithNothingAssumed) {
        List<Bounds> out = new ArrayList<>();
        add(out, seed);
        if (seed.min() != null) {
            add(out, new Bounds(seed.min(), null));
        }
        if (seed.max() != null) {
            add(out, new Bounds(null, seed.max()));
        }
        add(out, Bounds.spanning(seed, stepWithNothingAssumed));
        return out;
    }

    /** {@code one} added, unless it bounds nothing or is one already proposed. A range with neither
     * end is inductive for every step and proves nothing, so putting it through the proof is work
     * with a known answer. */
    private static void add(List<Bounds> out, Bounds one) {
        if (!one.isEmpty() && !out.contains(one)) {
            out.add(one);
        }
    }
}
