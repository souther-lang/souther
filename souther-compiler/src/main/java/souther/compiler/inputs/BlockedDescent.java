package souther.compiler.inputs;

/**
 * That the walk could not go on into what a position holds, and what stopped it.
 *
 * <p><b>An observation and not a state still to be settled.</b> The same stop reaches a reader two
 * ways: as {@link StructuralInspection.Continuation.Blocked}, which is what the position is left
 * with <em>if nothing else answers for it</em>, and as this, which stays true whatever answers
 * later. A body's rule may draw a line on the same position — a size, a length — and the position is
 * then measured, has no continuation left to be pending, and was still never entered. Read off the
 * continuation, that position came back with nothing to say the walk had stopped there
 * (issue #1084).
 *
 * <p>So this is the half of the stop that outlives the phase that found it. What a report says about
 * a position the walk could not enter is written from here and never from what the position is still
 * waiting on.
 *
 * <p><b>No axis.</b> Which axis carries the fact is settled where the axes are, and can change: one
 * position is measured at more than one number, and a body's rule re-points an axis at a term taken
 * of the position. An identity written in here would have to be rebuilt every time that happened,
 * and would be the wrong one for whoever asked afterwards.
 */
public record BlockedDescent(BlockReason.AboutThePosition why) {

    public BlockedDescent {
        if (why == null) {
            throw new IllegalArgumentException("a descent stopped by nothing is one that went on");
        }
    }

    /**
     * What {@code structure} found, or null where the walk went on.
     *
     * <p>Asked of the one structural reading rather than worked out again. A second reading of what
     * is under a position is the two disagreeing about whether it was entered, which is the shape of
     * mistake this type is here to close.
     */
    public static BlockedDescent of(StructuralInspection structure) {
        return structure instanceof StructuralInspection.Retained retained
                && retained.continuation()
                        instanceof StructuralInspection.Continuation.Blocked blocked
                ? new BlockedDescent(blocked.why())
                : null;
    }
}
