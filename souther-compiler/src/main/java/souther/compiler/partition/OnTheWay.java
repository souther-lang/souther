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
     * <p>Three shapes, and each says what this reading did rather than what the model says. A
     * condition an author wrote plainly is here wherever the arithmetic has no way of carrying it,
     * so nothing read off one of these says a row cannot be written, and a word going away is a
     * capability gained rather than a model changed.
     *
     * <p><b>Not the reason the same comparison gets for drawing no line.</b>
     * {@link UnreadComparison} answers why a comparison did not become a boundary, which is a
     * different question with different answers: {@code 1 < 2} comes back there as a form nothing
     * reads, when what happened is that it constrains no position; and a comparison this
     * arithmetic cannot carry comes back as one relating two positions, when a relation between two
     * positions is exactly what a cut over a {@code LinearForm} does carry. Borrowed here, either
     * would send an author after the wrong thing.
     *
     * <p>So what is said about a comparison is what is known about it here, and no more. The finer
     * answer belongs to whatever decided — {@link AffineReading}, which returns nothing and says
     * nothing about why — and it is not invented at this end from the shape of what it was given.
     */
    sealed interface Why {

        /** A condition that is neither a comparison nor a combination of them, so nothing was read
         *  of it. */
        record NoWordsForTheShape() implements Why {}

        /**
         * A comparison this reading did not turn into a cut.
         *
         * <p>One word, because one word is what this end knows. A comparison naming no position, a
         * form outside the arithmetic and a subject with no spacing for its values arrive here as
         * one absence, and {@link AffineReading} is where they would be told apart.
         */
        record ComparisonNotRepresentedAsACut() implements Why {}

        /**
         * What the condition coming out this way says is one of two things, and a region is what
         * has been accumulated onto it. {@code A && B} coming out false says one of them failed and
         * names neither, and taking either would exclude rows that arrive.
         */
        record OneOfTwoThings() implements Why {}
    }
}
