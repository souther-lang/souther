package souther.compiler.numeric;

import java.util.Collection;

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
 * <p><b>Nobody's vocabulary reaches here.</b> No operation's name, no term, no position, no
 * structural condition, and nothing saying whether a seed and a step are forms, trees or numbers.
 * What arrives is a {@link Prepared} reading answering four questions about ranges. Two readers ask
 * this — the one discharging a rule about a construction and the one measuring where a model divides
 * — and each projects its own words onto those four. What an operation starts from and repeats is
 * declared once, in {@code semantics.Accumulation}, and neither reader writes it down again; this is
 * the other half of that arrangement, and a theorem stated twice would be two statements to keep
 * true whose halves are free to part on the day one of them is sharpened.
 */
public final class Induction {

    private Induction() {}

    /** The range with no ends, which every walk's answer is in and which proves nothing. */
    public static final NumericDomain.Bounds ANYTHING = new NumericDomain.Bounds(null, null);

    /**
     * A caller's own reading of a walk, waiting to take in what the container guarantees.
     *
     * <p>One method, so what the proof reads is made once. The ranges worth trying are made from
     * what the step is handed, and the step is then checked against the very facts those ranges came
     * from: taken in through two entries instead, the two would be one adaptation written twice, and
     * a reader that took a fact in on one and not the other would prove less while looking complete.
     *
     * @param <D> whatever the caller reads its walk against
     */
    @FunctionalInterface
    public interface Reading<D> {

        /** This reading with what the container guarantees taken in. Asked once for a proof. */
        Prepared taking(D base);
    }

    /**
     * One walk, read against one set of assumptions.
     *
     * <p>The unit the proof works in. Everything it asks is asked of the same value, so what a
     * candidate was made from and what that candidate is checked against cannot be two readings.
     */
    public interface Prepared {

        /** Whether these assumptions hold nothing, in which case they settle nothing about a walk
         *  under them. */
        boolean isBottom();

        /** Where the value the walk starts from lies. */
        NumericDomain.Bounds seed();

        /** Where the step's answer lies, read against these assumptions. */
        NumericDomain.Bounds step();

        /** What holds of everything the step is handed besides the accumulator, each on its own.
         *  A walk carries its accumulator through what it was handed, so where the answer runs is
         *  where the two together run — which is a range worth trying and is why these are read. */
        Collection<NumericDomain.Bounds> whatTheStepIsHanded();

        /**
         * The same reading with the accumulator assumed to lie in {@code candidate}.
         *
         * <p>A fork, and never a widening of what the caller was reading before. Nothing derived
         * under an assumed accumulator is true where the accumulator is not assumed, so what comes
         * back is asked its {@link #step} and dropped.
         */
        Prepared assuming(NumericDomain.Bounds candidate);
    }

    /**
     * What the walk {@code reading} reads answers, as far as {@code base} settles it.
     *
     * <p>{@code base} is never written to: every candidate is checked against a reading forked from
     * it, and what comes back is a range and not a reading. So this can be asked twice with two
     * readings and answer twice, and neither answer can reach the other.
     */
    public static <D> NumericDomain.Bounds proves(D base, Reading<D> reading) {
        Prepared given = reading.taking(base);
        if (given.isBottom()) {
            return ANYTHING;   // a reading that holds nothing settles nothing about a walk under it
        }
        NumericDomain.Bounds seed = given.seed();
        // Every candidate proposed is one the seed lies in and every candidate proved was confirmed
        // to be, so each of these holds every value the seed does and so does the meet of them —
        // which is what lets the narrower of two be taken without asking whether it holds anything.
        // Taking it is what keeps the answer from depending on the order they were proposed in: a
        // generator lengthened later makes the answer sharper or leaves it alone.
        NumericDomain.Bounds proved = null;
        for (NumericDomain.Bounds candidate : InvariantCandidates.from(
                seed, given.step(), given.whatTheStepIsHanded())) {
            if (!inductive(given, candidate, seed)) {
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
     * <p>The step is read under the assumption and not before it. A step whose answer is arithmetic
     * a caller carries nothing about on its own — a product of the accumulator and an element — is
     * one that caller knows nothing of until what it was computed from is read, and what it was
     * computed from is the accumulator this is assuming a range for. Read without the assumption
     * instead, both factors are unknown and the product is unbounded whatever the candidate says, so
     * a walk that multiplies could never be proved. This is one reading of the step for one
     * candidate, not a round that feeds its own answer back.
     */
    private static boolean inductive(Prepared given, NumericDomain.Bounds candidate,
                                     NumericDomain.Bounds seed) {
        if (!seed.liesWithin(candidate)) {
            return false;
        }
        Prepared assuming = given.assuming(candidate);
        if (assuming.isBottom()) {
            // The accumulator is a value of its own, so a range for it cannot contradict a reading —
            // unless the reading already held nothing, which was answered before this was reached.
            throw new IllegalStateException("assuming a range for the accumulator left a reading that"
                    + " holds nothing, so the accumulator was not a value of its own");
        }
        return assuming.step().liesWithin(candidate);
    }
}
