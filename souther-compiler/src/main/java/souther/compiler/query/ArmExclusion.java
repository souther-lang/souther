package souther.compiler.query;

import souther.compiler.types.SourceConstructOrigin;

/**
 * Why an arm is outside the count.
 *
 * <p>An arm out of the count is one nothing can be owed over: what a row through it would establish
 * is not settled, so counting it would put a predicate in the denominator that the sentence over the
 * denominator does not hold of. It is not a gap and it is not a question the rows left open, and a
 * reader is told which arms these are and why.
 *
 * <p><b>What it carries, and which way it is read.</b> A weakening is derived from an exclusion and
 * never an exclusion from a weakening. What is uncertain here is a fact this account holds first —
 * the fork whose occurrences nothing tells apart — and the weakening is how that fact reaches a
 * measurement assembled over the account. Read the other way, every surface downstream would be
 * working out what an arm's state is from a set of reasons that were never about one arm.
 */
public sealed interface ArmExclusion {

    /**
     * The fork this is about, which is what tells one exclusion from another.
     *
     * <p>Of the fork and not of its arms. Both arms of one fork are out of the count together or
     * neither is, so a reader is told this once however many arms it holds.
     */
    SourceConstructOrigin fork();

    /** How this reaches a measurement assembled over the account. */
    Weakening weakening();

    /**
     * Two occurrences of one fork could not be told apart, so the arms counted as one arm are more
     * than one.
     *
     * <p>A fork whose declaration says the caller decides stands for as many obligations as there
     * are rules a caller handed in, and where nothing said which rule that was, one place can be
     * several. A row through either of them may or may not be a row through this one, so what its
     * arms come to is not a number over the arms an author wrote.
     */
    record OccurrencesNotToldApart(SourceConstructOrigin fork) implements ArmExclusion {

        @Override
        public Weakening weakening() {
            return new Weakening.ArmsUnsettled(fork);
        }
    }
}
