package souther.compiler.observe;

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

    /** The two answered differently: one answered and the other did not, or both answered values
     *  that are not the same value. */
    CHANGED,

    /** Both answered, and with the same value. */
    SAME,

    /** Nothing here can say: an answer could not be read in full, or neither program answered. */
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
            case AnswerObservation.NotAnswered _ -> COULD_NOT_TELL;
            case AnswerObservation.Answered(ObservedValue before) -> switch (now) {
                case AnswerObservation.NotAnswered _ -> CHANGED;
                case AnswerObservation.Answered(ObservedValue after) ->
                        before.unread() != null || after.unread() != null ? COULD_NOT_TELL
                                : same.of(before, after) ? SAME : CHANGED;
            };
        };
    }

    /** Whether two values, each read in full, are the same value. */
    @FunctionalInterface
    public interface SameValue {
        boolean of(ObservedValue left, ObservedValue right);
    }
}
