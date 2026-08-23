package souther.compiler.check;

import souther.compiler.core.Core;

/**
 * Whether an evaluation can answer, so that what is written after it is written after something.
 *
 * <p>A question about a transition and not about a place. An evaluation the walk reaches is
 * reached — the values it was computed from have answered and the walk is standing at it — and what
 * this says is whether any run that got that far carries a value on to what comes next. The two are
 * different points of the same program: {@code Int.divide(a, 0 - 1)} where {@code a} is the smallest
 * {@code Int} is an evaluation every run arrives at and none leaves.
 *
 * <p>Which is why the answer is not a state. Read as one, "this evaluation cannot answer" becomes
 * "nothing stands here", and a construction written among the values that evaluation is waiting on
 * would stop being judged — it is evaluated before the abort and is a construction the program
 * really builds. What the state records is the continuation ({@link Known#reachingNothing}), and it
 * is given that only where the transition into it is one nothing makes.
 *
 * <p>Two answers and not three. {@link MayComplete} is the {@code may} of a reading that
 * over-approximates: it says this analysis did not show that no run leaves, and never that a run
 * does. Read as the second it would be a claim about a value existing, which nothing here proves —
 * a range holding values may still be a range the operation reaches none of.
 */
sealed interface Completion {

    /** Nothing here showed that no run carries a value on from this evaluation. */
    record MayComplete() implements Completion {}

    /** No run does, and {@code proof} is what showed it. */
    record CannotComplete(NoCompletionProof proof) implements Completion {}

    Completion MAY = new MayComplete();

    /**
     * How it was shown that an evaluation answers nothing.
     *
     * <p>Kept as a value, and kept as a family. The check that acts on it does not read it: it makes
     * the continuation one nothing reaches and says nothing at all, because what to tell an author
     * about an evaluation no run leaves is a question about diagnostics — which expression to blame,
     * whether it is an error or a warning, what to do where one abort stands inside another — and
     * settling it here would tie a reporting policy to the mechanism a second time. A reader that
     * wants to say it later reads this instead of working the reasons out again, one primitive at a
     * time.
     *
     * <p>A family because the reasons are unalike and more of them are coming. What is common is the
     * consequence, which is this interface; what differs is everything a sentence about it would
     * say.
     */
    sealed interface NoCompletionProof {

        /**
         * The arithmetic {@code operation} computes answers a number no value of its type is, for
         * every operand this reading admits — and the case it would otherwise come back as cannot
         * come back here either.
         */
        record NoValue(Core operation, FactSubject answer) implements NoCompletionProof {}

        /**
         * {@code made} fails its type's invariant on every path read here, so building it aborts.
         *
         * <p>Not an attempted construction, which is the other thing entirely: a failing invariant
         * there is the departure being taken, and a departure is a run carrying on.
         */
        record RefutedConstruction(Core.Construct made) implements NoCompletionProof {}
    }
}
