package souther.compiler.observe;

import java.util.Objects;

/**
 * What a run of a behavior answered, as a fact about the run and nothing about what it is held to.
 *
 * <p>Two cases and not a value that may be missing, because the absence is a fact of its own. A run
 * that never got an answer back — it aborted, it ran out of budget, nothing could apply it — has
 * nothing to compare, and a run that answered with a value this compiler could not read did answer:
 * the second is {@link Answered} of an {@link ObservedValue.Unknown}, and a reader that wants to
 * know whether two runs answered alike is at the end of what it can say in both, for different
 * reasons. Folded into one, a row that aborted would read as one whose answer was unreadable.
 *
 * <p>Nothing here says what the answer is compared with or at which grain. That is the row's to
 * decide — a row that names a case is held to the case and one that writes a value to the value —
 * and a reading of this that compared more than the row states would be crediting the row with a
 * difference it does not notice.
 */
public sealed interface AnswerObservation {

    /** No answer came back from the run: it stopped without one, or nothing applied it. */
    record NotAnswered() implements AnswerObservation {}

    /**
     * The run went past what a run may spend — its steps, its depth, its stack or its time — before
     * it answered. Apart from {@link NotAnswered} because it says nothing about the program: a run
     * given more might answer, so whether it answers as another run does is not known, where a run
     * that stopped is known to have answered nothing.
     */
    record RanOut() implements AnswerObservation {}

    /** The run answered, and this is the answer as the compiler owns it. */
    record Answered(ObservedValue value) implements AnswerObservation {

        public Answered {
            Objects.requireNonNull(value, "an answer is a value, or says why it could not be read");
        }
    }
}
