package souther.compiler.partition;

import souther.compiler.diag.Citation;
import souther.compiler.inputs.TermPath;

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
 * <p><b>Every condition is one of these, and which is not a choice about the shape it was written
 * in.</b> A condition either lands in a vocabulary a search can compose against — the arithmetic's
 * ({@link TakenIn}) or the positions' ({@link Narrowed}) — or it is {@link Declined}. So a fork this
 * reading learns to walk later widens what a search can reach and can never quietly leave a
 * condition off: a reader that cannot state one says so here, and a row composed under a declined
 * condition is a row that may not arrive rather than a row nothing knew about.
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

    /**
     * A condition that says which values a position is one of, as the position it narrows.
     *
     * <p>What a fork on a sum states. Reaching the arm is the scrutinee having turned out to be the
     * case the arm selects, and that is a narrowing of the position the scrutinee is at — which is
     * a thing a row can be composed to be, while "this arm was taken" is not.
     *
     * <p>The narrowed position and not the pair it is made of. What has to hold of the parameter
     * for such a position to exist in it is {@link TermPath#requirements()}, which is where every
     * other reader of a narrowing asks; carried as a position and a refinement side by side, this
     * would be the one place that splits them its own way.
     *
     * @param position the scrutinee's position with the arm's case narrowed onto it
     */
    record Narrowed(Citation at, TermPath position) implements OnTheWay {

        public Narrowed {
            if (position == null || !position.narrowsWhatItReaches()) {
                throw new IllegalArgumentException(
                        "a narrowing on the way is a position read as one of its cases: " + position);
            }
        }
    }

    /** A condition nothing here could turn into a cut, and what stopped it. */
    record Declined(Citation at, Why why) implements OnTheWay {}

    /**
     * What stopped a condition on the way from bearing on where a row was looked for.
     *
     * <p>Two stages and one list, because an author reading it wants the same thing from both: a
     * condition the walk could not state, and a condition it stated that nothing could compose a
     * value under, leave the same gap between what a row was built to be and what reaches the
     * border. Kept apart, one of them would be the half that is never printed.
     *
     * <p>Each says what this compiler did rather than what the model says. A condition an author
     * wrote plainly is here wherever nothing here has a way of carrying it, so nothing read off one
     * of these says a row cannot be written, and a word going away is a capability gained rather
     * than a model changed.
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

        /**
         * An arm of a fork this reading could not state as a narrowing of a position.
         *
         * <p>A fork on something no position holds — an expression the walk cannot follow back to
         * one, an arm answering for several cases at once, a case the reading of the declarations
         * has no position for. Each of those leaves the same thing unsaid, which is which values of
         * the input reach this arm, so they arrive here as one word.
         */
        record ForkArmNotReadAsANarrowing() implements Why {}

        /**
         * A cut the walk took in that nothing could put a value under.
         *
         * <p>Said of the whole cut, because a cut over two positions is one statement about the
         * pair. One of them put where the cut admits and the other left to its own declared range
         * is not half of the condition holding — it is the condition not holding, with a position
         * pinned on the strength of it. So a cut this cannot place every position of is placed at
         * none of them, and the fact that it was handed one it could not act on is here.
         */
        record NoValueComposedForItsPositions() implements Why {}
    }
}
