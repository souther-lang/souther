package souther.compiler.observe;

import souther.compiler.types.SourceConstructOrigin;

import java.util.Objects;

/**
 * One run of a row with one arm of the body answering with a sibling's expression instead.
 *
 * <p>What a row is asked in order to find out whether the arm it went through decides its answer.
 * The row is run again exactly as written, with arm {@link #part} of {@link #fork} answering with
 * arm {@link #with}, and held to what it states as it was the first time. A row that would not
 * notice the arm being written as its sibling is not evidence for the arm, however surely it goes
 * through it.
 *
 * <p>Two findings and not one, because they answer different questions. {@link #answer} is what the
 * replaced program answered, which says whether the replacement changed anything at all; {@link
 * #noticed} is whether the row's own statement told the difference, which a row naming only the
 * case cannot do for a value under it.
 *
 * @param fork   the fork whose arm was replaced, as the author wrote it
 * @param part   which of its arms
 * @param with   which sibling answered in its place
 * @param answer what the run answered
 * @param noticed whether what the row states told the replaced program from the written one
 */
public record ReplacedRun(SourceConstructOrigin fork, int part, int with,
                          AnswerObservation answer, Noticed noticed) {

    public ReplacedRun {
        Objects.requireNonNull(fork, "an arm is an arm of some fork");
        Objects.requireNonNull(answer, "a run says what it answered, or that it answered nothing");
        Objects.requireNonNull(noticed, "a run says whether the row noticed, or why it cannot");
        if (part == with) {
            throw new IllegalArgumentException("an arm replaced by itself is the arm: part " + part
                    + " of " + fork);
        }
    }

    /** Whether the row told the replaced program from the written one. */
    public enum Noticed {
        /** The row failed: what it states does not hold of the replaced program. */
        YES,
        /** The row held: what it states holds of the replaced program as well. */
        NO,
        /** The row's answer is owed, so it states nothing a difference could fail. */
        STATES_NOTHING,
        /** The run did not come to an answer this compiler could hold the row to: it ran out of
         *  time or budget. Not a finding about the row. */
        COULD_NOT_TELL
    }
}
