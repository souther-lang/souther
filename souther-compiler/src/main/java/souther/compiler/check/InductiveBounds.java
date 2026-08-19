package souther.compiler.check;

import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;

import java.util.List;
import java.util.Map;

/**
 * What a walk from a seed answers, proved by checking a range rather than by running the walk.
 *
 * <p>A reduction answers {@code a}, where {@code a} is the seed or is the step applied to an earlier
 * accumulator and something the container held. So a range holds the answer if the seed is in it and
 * the step, given an accumulator in it and inputs the container guarantees, answers inside it again.
 * Two questions, each asked once. There is no iteration to a fixed point, no widening, nothing read
 * off how long the container is, and no expansion of the walk — a range is proposed, and it is
 * checked, and that is the whole of it.
 *
 * <p>Which ranges are proposed is not here ({@link InvariantCandidates}). Nothing about soundness
 * depends on that list, which is the point of the split: a guess that cannot be proved costs a check
 * and is discarded, so the list may be lengthened by anyone without this being read again.
 *
 * <p>What it proves is conditional and the condition is not this check's to discharge: <em>if the
 * reduction answers at all, its answer is in the range</em>. A step that aborts part way — an
 * addition past what an {@code Int} holds — answers nothing, and a range that says where an answer
 * lies says nothing about a run that produces none. Whether the arithmetic can abort is the
 * arithmetic check's question and whether the walk terminates is the totality check's, and neither
 * is weakened by this and neither is assumed by it.
 *
 * <p>No operation's name reaches here. What arrives is a seed, an accumulator, a step, and facts
 * about what the step is handed — so an operation the library gains that reduces the same way is
 * proved by this unchanged.
 */
final class InductiveBounds {

    private InductiveBounds() {}

    /**
     * A walk, as the numbers it is made of: what it starts from, what the accumulator is called while
     * the step runs, what the step answers, and what holds of everything else the step is handed.
     *
     * <p>Forms and atoms, read where the walk was named. Nothing here is a tree to be read again, and
     * nothing here holds an environment: what could be read of the walk was read then, and a walk
     * whose parts could not be read that way is not one of these at all.
     */
    record Walk(LinearForm<FactSubject> seed, FactSubject accumulator,
                LinearForm<FactSubject> step, StepInputFacts inputs) {}

    /** The range with no ends, which every walk's answer is in and which proves nothing. */
    static final Bounds ANYTHING = new Bounds(null, null);

    /**
     * What {@code walk} answers, as far as {@code base} settles it.
     *
     * <p>{@code base} is the reading the question was asked under and is never written to: every
     * candidate is checked against a domain forked from it, and what comes back is a range and not a
     * domain. So this can be asked twice with two readings and answer twice, and neither answer can
     * reach the other.
     */
    static Bounds provenOf(Walk walk, NumericDomain<FactSubject> base, Terms terms) {
        NumericDomain<FactSubject> given = walk.inputs().taking(base);
        if (given.isBottom()) {
            return ANYTHING;   // a reading that holds nothing settles nothing about a walk under it
        }
        Bounds seed = given.boundsOf(walk.seed());
        Bounds proved = null;
        for (Bounds candidate : InvariantCandidates.from(seed, given.boundsOf(walk.step()))) {
            if (!inductive(walk, candidate, seed, given, terms)) {
                continue;
            }
            proved = proved == null ? candidate : narrower(proved, candidate);
        }
        return proved == null ? ANYTHING : proved;
    }

    /**
     * Whether the answer cannot leave {@code candidate}: the seed is inside it, and a step given an
     * accumulator inside it answers inside it.
     *
     * <p>The domain the step is read against is forked from the one the caller was given and is
     * dropped here. Nothing derived under an assumed accumulator is true where the accumulator is
     * not assumed, so letting it back would be this deriving from its own answers — which is what
     * {@link DerivedBounds} declines to be and for the same reason.
     */
    private static boolean inductive(Walk walk, Bounds candidate, Bounds seed,
                                     NumericDomain<FactSubject> given, Terms terms) {
        if (!seed.liesWithin(candidate)) {
            return false;
        }
        Map<FactSubject, Granularity> spacing = terms.kindsOf(LinearForm.atom(walk.accumulator()));
        NumericDomain<FactSubject> assuming = given.assuming(walk.accumulator(), candidate, spacing);
        if (assuming.isBottom()) {
            // The accumulator is an atom of its own, so a range for it cannot contradict a reading —
            // unless the reading already held nothing, which was answered before this was reached.
            throw new IllegalStateException("assuming a range for the accumulator left a reading that"
                    + " holds nothing, so the accumulator was not a value of its own");
        }
        return assuming.boundsOf(walk.step()).liesWithin(candidate);
    }

    /**
     * The narrower of two ranges a walk's answer was proved to be in.
     *
     * <p>Both are true of the answer, so their intersection is too, and taking it is what keeps the
     * result from depending on the order the candidates were proposed in — a generator lengthened
     * later then makes the answer sharper or leaves it alone, and never changes it.
     *
     * <p>It holds something, and that is argued rather than checked. Every candidate proposed is one
     * the seed lies in, and a candidate is only proved after that has been confirmed, so both of
     * these hold every value the seed does and so does what is between them.
     */
    private static Bounds narrower(Bounds a, Bounds b) {
        return new Bounds(Endpoint.lower(a.min(), b.min()), Endpoint.upper(a.max(), b.max()));
    }

    /** Whether a walk's answer was settled at all, which is what a caller takes as holding — a range
     * with no ends is what this answers when nothing was proved, and asserting it into a domain would
     * be asserting nothing under the name of a derivation. */
    static boolean settles(Bounds proven) {
        return !proven.isEmpty();
    }

    /** For the tests that read which ranges a walk was proposed, without going through a program. */
    static List<Bounds> candidatesFor(Bounds seed, Bounds stepWithNothingAssumed) {
        return InvariantCandidates.from(seed, stepWithNothingAssumed);
    }
}
