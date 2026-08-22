package souther.compiler.partition;

import souther.compiler.diag.Citation;

/**
 * One condition on the way to a comparison, and what became of it.
 *
 * <p>Both halves, because a region says nothing about how it was arrived at. What the walk took in
 * is what narrowed the search; what it could not take in is why the search may be looking over rows
 * that never arrive. Kept as one sequence in the order the walk met them, so that a reader asking
 * either question asks the same list — split into two at the seam, "nothing stood on the way" and
 * "everything on the way was taken in" come out as the same empty answer, which is the reading a
 * report cannot make and the one an author needs.
 *
 * <p>Collected where the condition is met and never worked out afterwards from where a comparison
 * sits, which is the rule {@link souther.compiler.reach.PathDecision} is written to as well.
 */
public sealed interface OnTheWay {

    /**
     * Where the condition is, as a report is entitled to say it.
     *
     * <p>A {@link Citation} and not a {@link souther.compiler.diag.SourcePos}, because what this is
     * for is being said. Whether a reader can be sent to the text and whether the condition is
     * written at the place are the two questions that type answers, and a helper's condition
     * reached from a call is exactly where a raw position sends a reader somewhere the code is not.
     */
    Citation at();

    /** A condition the arithmetic took in, and the cut it came to. */
    record TakenIn(Citation at, ReachingCuts.Cut cut) implements OnTheWay {}

    /** A condition nothing here could turn into a cut, and what stopped it. */
    record Declined(Citation at, Why why) implements OnTheWay {}

    /**
     * What stopped a condition from becoming a cut.
     *
     * <p>Every one of these is a limit of this compiler and none of them is a fact about the model:
     * a condition an author wrote plainly is on this list wherever the arithmetic here has no way
     * of carrying it. Which is why nothing read off one of these says a row cannot be written, and
     * why a word here going away is a capability gained rather than a model changed.
     *
     * <p>Its own set, and not {@link souther.compiler.inputs.BlockReason.AboutARule}. That one is
     * about one rule this read and could not use, and it answers for whether a measure is thereby
     * short of something. An arm of a fork stating one of two things is neither: there is no single
     * rule to name, and the measures are not short — the line is still owed and still measured, and
     * what is affected is where a row for it was looked for.
     */
    enum Why {

        /** A condition of a shape this reading has no words for, so nothing was read of it. */
        CONDITION_NOT_READ,

        /** Read as far as it goes, and it states nothing about any position of the input. */
        NO_CONSTRAINT_REPRESENTED,

        /**
         * What the condition coming out this way says is one of two things, and a region is what
         * has been accumulated onto it. {@code A && B} coming out false says one of them failed and
         * names neither, and taking either would exclude rows that arrive.
         */
        NON_CONJUNCTIVE_OUTCOME
    }
}
