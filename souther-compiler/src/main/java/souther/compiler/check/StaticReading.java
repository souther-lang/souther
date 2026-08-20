package souther.compiler.check;

/**
 * One thing a finished reading made of a clause.
 *
 * <p>A reading and not a representation, and the name is doing work. {@link AsABound} says this
 * compiler carried the clause into a form a guard can be held against; it does not say the clause is
 * discharged. Whether a construction is judged safe is asked at the construction, from what the
 * guards on that path established, and is {@link Predicates.Clause}'s to answer. Named for the
 * representation, {@code AsABound} would read as "discharged" the first time somebody needed it to,
 * and a report would say a construction was proven by a classification that never saw one.
 *
 * <p>More than one where more than one is true of a clause. What is written as one thing need not be
 * read as one thing — a clause naming a helper is one thing to its author and is whatever that
 * helper states to the check — and the readings need not agree: a bound and a term the check can
 * only compare for identity are discharged by different guards, and one of them being there says
 * nothing about the other. Answering with one of them is choosing which half of a clause to
 * describe, and the half not chosen is the one an author is about to be surprised by.
 */
public sealed interface StaticReading {

    /**
     * A relation the numeric domain reasons over, so any guard that <em>implies</em> it discharges
     * the clause at a construction.
     */
    record AsABound() implements StaticReading {}

    /**
     * A term the check can name but not reason about, so a guard establishing the same canonical
     * property discharges it and nothing weaker does.
     */
    record AsATerm() implements StaticReading {}

    /**
     * The clause settled on its own, before any construction was looked at.
     *
     * <p>{@code invariant 1 >= 0} holds of every value and asks nothing of a guard.
     * {@code invariant 1 < 0} holds of none, so no guard establishes it and no value of the type can
     * be built. Both are answers a reading reached, and neither is a clause this compiler could not
     * read — which is what both of them used to be reported as, in opposite directions: the first
     * came back as a clause outside the fragment, and the second as a bound any guard implying it
     * would discharge, when there is no such guard.
     *
     * <p>Both signs here, and not the true one with the false one left to fall wherever it falls.
     * They come from one fold of one expression. Split, the half nobody wrote down goes to whichever
     * arm is nearest, which is how the false one became a bound.
     *
     * <p>What an author should be told about {@code Decided(false)} — a line in an editor, a
     * diagnostic at the declaration, or a type nothing inhabits — is a separate question, and one
     * about the language rather than about this accounting. What is settled here is that the answer
     * is kept as what it is.
     *
     * @param holds which way it folded
     */
    record Decided(boolean holds) implements StaticReading {}

    /**
     * The reading finished, and this part of the clause is outside what it reads.
     *
     * <p>A conclusion, which is why it is here and not beside
     * {@link CapabilityResult.AnalysisStopped}. Something that stopped concluded nothing about the
     * fragment, and putting it in this arm is the one sentence the split exists to keep out.
     */
    record OutsideTheFragment(FragmentReason why) implements StaticReading {

        public OutsideTheFragment {
            if (why == null) {
                throw new IllegalArgumentException("a reading that stopped short says what stopped it");
            }
        }
    }
}
