package souther.compiler.partition;

import souther.compiler.diag.Citation;
import souther.compiler.inputs.BlockReason;

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
     * <p>Three shapes, and only one of them has a rule to name. A condition this reading has no
     * words for is not one thing an author wrote; an arm of a fork stating one of two things is
     * about the arm and not about either operand; and a comparison read and not used is a rule,
     * which is why that one carries the account of it rather than a word of its own.
     *
     * <p><b>The comparison's reason is the one this compiler already gives.</b>
     * {@link souther.compiler.inputs.BlockReason.AboutARule} is what a reading of a rule it could
     * not use comes to, and {@link UnreadComparison} is where a comparison is turned into one — the
     * same answer the line beside this one is filed under. A word invented here would be a second
     * classification of one question: it merged a form outside the arithmetic, a carrier no line is
     * drawn on and a comparison relating two positions into one sentence, and called all three a
     * limit of this compiler when the last is what the rule says.
     *
     * <p>Which of these leaves a region wider than the rows that arrive is not answered here and is
     * not the same question as {@link souther.compiler.inputs.BlockReason.AboutARule#leavesShort},
     * which is about a measure. A condition that did not narrow the region may still be implied by
     * one that did.
     */
    sealed interface Why {

        /** A condition of a shape this reading has no words for, so nothing was read of it. */
        record NoWordsForTheShape() implements Why {}

        /**
         * One comparison it read and could not use, in the words that already answer that.
         *
         * @param why what {@link UnreadComparison} makes of it, which is what the same comparison
         *            is filed under wherever else this compiler says it could not use one
         */
        record ARuleItCouldNotUse(BlockReason.AboutARule why) implements Why {

            public ARuleItCouldNotUse {
                if (why == null) {
                    throw new IllegalArgumentException(
                            "a rule this could not use is one a reader can be told about");
                }
            }
        }

        /**
         * What the condition coming out this way says is one of two things, and a region is what
         * has been accumulated onto it. {@code A && B} coming out false says one of them failed and
         * names neither, and taking either would exclude rows that arrive.
         */
        record OneOfTwoThings() implements Why {}
    }
}
