package souther.compiler.observe;

import souther.compiler.partition.Replacement;

import java.util.List;
import java.util.Objects;

/**
 * One run of a row with the body rewritten: an arm answering with a sibling's expression instead,
 * or a walk run another way.
 *
 * <p>What a row is asked in order to find out whether what it went through decides its answer. The
 * row is run again exactly as written, under {@link #replaced}, and held to what it states as it was
 * the first time. A row that would not notice the arm being written as its sibling, or the walk
 * stopping after one step, is not evidence for the arm or the walk, however surely it goes through
 * it.
 *
 * <p>Two findings and not one, because they answer different questions. {@link #answer} is what the
 * rewritten program answered, which says whether the rewrite changed anything at all; {@link
 * #noticed} is whether the row's own statement told the difference, which a row naming only the
 * case cannot do for a value under it.
 *
 * @param replaced which rewrite the run was of: an arm's or a walk's, never the body answering one
 *                 value, which is no program a run is made of
 * @param answer   what the run answered
 * @param changed  whether that is a different answer from the one the written program gave the
 *                 row, which is what shows the rewrite matters on this input whatever the row
 *                 states
 * @param noticed  whether what the row states told the rewritten program from the written one
 * @param untoldAt where {@code noticed} could not tell, the figures of this compiler's that stopped
 *                 the rewritten run, each as it stood where the run was compared against it; none
 *                 where nothing that stopped it was a figure, and none where it could tell
 */
public record ReplacedRun(Replacement replaced, AnswerObservation answer, AnswerChange changed,
                          Noticed noticed, List<Figure> untoldAt) {

    public ReplacedRun {
        Objects.requireNonNull(replaced, "a run is of some rewrite");
        if (replaced instanceof Replacement.ByOneAnswer) {
            throw new IllegalArgumentException("a body answering one value is no program a run is"
                    + " made of: " + replaced);
        }
        Objects.requireNonNull(answer, "a run says what it answered, or that it answered nothing");
        Objects.requireNonNull(changed, "a run says whether its answer changed, or that it cannot");
        Objects.requireNonNull(noticed, "a run says whether the row noticed, or why it cannot");
        untoldAt = Figure.inOrder(untoldAt);
        if (!untoldAt.isEmpty() && noticed != Noticed.COULD_NOT_TELL) {
            throw new IllegalArgumentException("a figure stopped a run the row was told by: "
                    + untoldAt);
        }
    }

    /** Whether the row told the rewritten program from the written one. */
    public enum Noticed {
        /** The row ended the other way: it holds of one of the two programs and fails of the
         *  other. */
        YES,
        /** The row ended the same way: it holds of both, or fails of both. */
        NO,
        /** The row's answer is owed, so it states nothing a difference could fail. */
        STATES_NOTHING,
        /** The run did not come to an answer this compiler could hold the row to: it ran out of
         *  time or budget. Not a finding about the row. */
        COULD_NOT_TELL
    }
}
