package souther.compiler.observe;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * Whether a program answered one input differently from another program, which is what a
 * replacement of a body is shown to matter by.
 *
 * <p>A question about the two programs and not about any row. Whether a row would notice is what
 * the row states, asked of it ({@link ReplacedRun#noticed}); this is whether there was anything to
 * notice at all, and a replacement that changes nothing on any input is one no row can be asked to
 * tell apart.
 */
public enum AnswerChange {

    /** The two answered differently: one answered and the other stopped without answering, or both
     *  answered values that are not the same value. */
    CHANGED,

    /** Both answered, and with the same value. */
    SAME,

    /** Nothing here can say: an answer could not be read in full, a run ran past what a run may
     *  spend, or the first program did not answer. */
    COULD_NOT_TELL;

    /**
     * What the two answers come to, given whether two values that are both there are the same.
     *
     * <p>Every case but the last is settled by whether each answered and was read in full, so a
     * caller asks only the question that needs the declarations.
     */
    public static AnswerChange between(AnswerObservation was, AnswerObservation now,
                                       SameValue same) {
        return switch (was) {
            case AnswerObservation.NotAnswered _, AnswerObservation.RanOut _ -> COULD_NOT_TELL;
            case AnswerObservation.Answered(ObservedValue before) -> switch (now) {
                case AnswerObservation.NotAnswered _ -> CHANGED;
                // A run that ran out is not one that answered otherwise: given more it might
                // answer as the other did.
                case AnswerObservation.RanOut _ -> COULD_NOT_TELL;
                case AnswerObservation.Answered(ObservedValue after) ->
                        // Read in full everywhere inside, which is what a comparison of two values
                        // asks of each: a record read whole may hold a list cut short.
                        !Limits.UNBOUNDED.admits(before) || !Limits.UNBOUNDED.admits(after)
                                ? COULD_NOT_TELL
                                : same.of(before, after) ? SAME : CHANGED;
            };
        };
    }

    /**
     * The figures that left {@link #between} unable to say, each as it stood where it was reached:
     * a run that went past one, or an answer a figure kept from being read in full. None where
     * nothing that stopped it was a figure — a run that answered nothing, an answer nothing could
     * read, the host's stack — and none where it could say.
     *
     * <p>Read off the same cases {@code between} reads, so the figures are of the answers it was
     * handed and not of another reading of them.
     */
    public static List<Figure> untoldAt(AnswerObservation was, AnswerObservation now) {
        return switch (was) {
            case AnswerObservation.NotAnswered _ -> List.of();
            case AnswerObservation.RanOut(Optional<Figure> limit) -> limit.stream().toList();
            case AnswerObservation.Answered(ObservedValue before) -> switch (now) {
                case AnswerObservation.NotAnswered _ -> List.of();
                case AnswerObservation.RanOut(Optional<Figure> limit) -> limit.stream().toList();
                case AnswerObservation.Answered(ObservedValue after) -> {
                    List<Figure> out = new ArrayList<>();
                    for (ObservedValue each : List.of(before, after)) {
                        Incompleteness.Cause stopped = Limits.UNBOUNDED.stoppedBy(each);
                        if (stopped != null) {
                            stopped.figure().ifPresent(out::add);
                        }
                    }
                    yield Figure.inOrder(out);
                }
            };
        };
    }

    /** Whether two values, each read in full, are the same value. */
    @FunctionalInterface
    public interface SameValue {
        boolean of(ObservedValue left, ObservedValue right);
    }
}
