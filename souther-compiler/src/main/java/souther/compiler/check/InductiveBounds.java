package souther.compiler.check;

import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;

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

    /**
     * What a form lies between in a domain, with the arithmetic its atoms stand for read against
     * that same domain.
     *
     * <p>Taken rather than done here, because which recipes an atom has is
     * {@link DerivedNumericFacts}' table and reading it a second way would be a second answer. What this
     * asks of it is the part that matters to a proof: the domain is the one the question is asked
     * in, so a product inside a step is read under the induction hypothesis and not under what was
     * known before it.
     */
    @FunctionalInterface
    interface Reading {

        Bounds of(LinearForm<FactSubject> form, DerivedNumericFacts.ReadingDomain domain);
    }

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
    static Bounds provenOf(Walk walk, DerivedNumericFacts.ReadingDomain base, Terms terms,
                           Reading read) {
        DerivedNumericFacts.ReadingDomain given = base.taking(walk.inputs());
        if (given.isBottom()) {
            return ANYTHING;   // a reading that holds nothing settles nothing about a walk under it
        }
        Bounds seed = read.of(walk.seed(), given);
        // Every candidate proposed is one the seed lies in and every candidate proved was confirmed
        // to be, so each of these holds every value the seed does and so does the meet of them —
        // which is what lets the narrower of two be taken without asking whether it holds anything.
        // Taking it is what keeps the answer from depending on the order they were proposed in: a
        // generator lengthened later makes the answer sharper or leaves it alone.
        Bounds proved = null;
        for (Bounds candidate : InvariantCandidates.from(
                seed, read.of(walk.step(), given), walk.inputs().at().values())) {
            if (!inductive(walk, candidate, seed, given, terms, read)) {
                continue;
            }
            proved = proved == null ? candidate : proved.meet(candidate);
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
     * {@link DerivedNumericFacts} declines to be and for the same reason.
     *
     * <p>The step is read in that forked domain and not before it. A step whose answer is arithmetic
     * the fragment cannot carry — {@code acc * x.value} — is one value the domain holds nothing
     * about until what it was computed from is read, and what it was computed from is the
     * accumulator this is assuming a range for. Read against the caller's domain instead, both
     * factors are unknown and the product is unbounded whatever the candidate says, so a walk that
     * multiplies could never be proved. This is one reading of the step for one candidate, not a
     * round that feeds its own answer back.
     */
    private static boolean inductive(Walk walk, Bounds candidate, Bounds seed,
                                     DerivedNumericFacts.ReadingDomain given, Terms terms,
                                     Reading read) {
        if (!seed.liesWithin(candidate)) {
            return false;
        }
        Map<FactSubject, Granularity> spacing = terms.kindsOf(LinearForm.atom(walk.accumulator()));
        DerivedNumericFacts.ReadingDomain assuming =
                given.assuming(walk.accumulator(), candidate, spacing);
        if (assuming.isBottom()) {
            // The accumulator is an atom of its own, so a range for it cannot contradict a reading —
            // unless the reading already held nothing, which was answered before this was reached.
            throw new IllegalStateException("assuming a range for the accumulator left a reading that"
                    + " holds nothing, so the accumulator was not a value of its own");
        }
        return read.of(walk.step(), assuming).liesWithin(candidate);
    }
}
