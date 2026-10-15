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
     * What left {@link #between} unable to say, or null where it could.
     *
     * <p>Asked of both answers, each for what keeps it from being one the two could be told by: a
     * run that went past a figure or stopped of its own accord, or an answer that could not be read
     * in full. The first program answering nothing is one of those — nothing can be told against
     * it — and the second answering nothing is not: against an answer, that is an answer that
     * changed. Both are asked even where {@code between} stopped at the first, because a run that
     * gets past the first meets the second.
     */
    public static Untold untold(AnswerObservation was, AnswerObservation now) {
        // An answer against nothing is an answer that changed, however much of it was read.
        if (was instanceof AnswerObservation.Answered && now instanceof AnswerObservation.NotAnswered) {
            return null;
        }
        Untold out = keptFromTelling(was, true).and(keptFromTelling(now, false));
        return out.equals(Untold.NOTHING) ? null : out;
    }

    /** What keeps one answer from being one a pair is told by. */
    private static Untold keptFromTelling(AnswerObservation answer, boolean nothingIsUntold) {
        return switch (answer) {
            case AnswerObservation.NotAnswered _ ->
                    nothingIsUntold ? Untold.AT_NO_FIGURE : Untold.NOTHING;
            case AnswerObservation.RanOut(Optional<Figure> limit) ->
                    limit.map(Untold::at).orElse(Untold.AT_NO_FIGURE);
            case AnswerObservation.Answered(ObservedValue value) -> {
                Incompleteness.Cause stopped = Limits.UNBOUNDED.stoppedBy(value);
                yield stopped == null ? Untold.NOTHING
                        : stopped.figure().map(Untold::at).orElse(Untold.AT_NO_FIGURE);
            }
        };
    }

    /**
     * What kept two answers from being told apart: the figures of this compiler's each was stopped
     * at, as each stood where it was reached, and whether something no figure decides kept one of
     * them as well — a run that answered nothing, an answer nothing could read, the host's stack.
     *
     * <p>Both where both happened. A reader told only the figure would be told nothing else stood
     * in the way, and one told only the rest would not know a figure was reached.
     *
     * @param figures    every figure, each once and in {@link Figure#inOrder}
     * @param atNoFigure whether something no figure decides kept them as well
     */
    public record Untold(List<Figure> figures, boolean atNoFigure) {

        private static final Untold NOTHING = new Untold(List.of(), false);

        private static final Untold AT_NO_FIGURE = new Untold(List.of(), true);

        public Untold {
            figures = Figure.inOrder(figures);
        }

        private static Untold at(Figure figure) {
            return new Untold(List.of(figure), false);
        }

        private Untold and(Untold other) {
            List<Figure> both = new ArrayList<>(figures);
            both.addAll(other.figures);
            return new Untold(both, atNoFigure || other.atNoFigure);
        }
    }

    /** Whether two values, each read in full, are the same value. */
    @FunctionalInterface
    public interface SameValue {
        boolean of(ObservedValue left, ObservedValue right);
    }
}
