package souther.compiler.partition;

/**
 * A position the local producers were all asked about that none of them answered, and what it is
 * left with so far.
 *
 * <p>The step before a verdict, and the only way to an absence. Holding one of these is already
 * three facts: the position was read, the producers of local evidence came back with nothing, and
 * the structural reading has said whether it stopped. What is missing is what the rules written
 * about the position came to, which {@link #complete} takes.
 *
 * <p>Which is what makes an absence a conclusion rather than a default. Written as a value anything
 * could construct, "the model divides this position no way" was one line of a caller away from
 * every position that happened to have an empty list beside it, and the whole protocol exists
 * because that line was easy to write.
 *
 * <p>Package-private, cases and all, so that the chain cannot be started halfway through from
 * outside. Inside this package it is a discipline like any other and the tests hold it; outside,
 * there is no {@code Leaf} to make and so no absence to reach.
 */
sealed interface PendingPosition {

    TermPath at();

    /**
     * Nothing under the position, and nothing stopped the reading of it.
     *
     * <p>Not an absence. Whether the position divides is still open — the rules a body writes have
     * not been read at this point — and this is the one state from which an absence can follow.
     */
    record Leaf(TermPath at) implements PendingPosition {}

    /**
     * The structural reading stopped, and this is what the position is left with unless something
     * else answers for it.
     *
     * <p>Carried rather than reported: a rule a body writes may still draw a line on this same
     * position, and where one does the position is measured and this is never said.
     */
    record Blocked(TermPath at, BlockReason why) implements PendingPosition {}

    /**
     * What is still to be answered for at {@code axis}, or null where the axis has evidence.
     *
     * <p>Null and not a case, because a position with evidence is not pending anything: it is
     * measured, and the question this type is about does not arise for it. Which is also why
     * {@link #complete} refuses a body that says it drew a line — two readings would then disagree
     * about whether this position has evidence.
     */
    static PendingPosition of(Axis axis) {
        if (axis.measurable()) {
            return null;
        }
        return switch (axis.pending()) {
            // The structural stop outranks a rule the local reading could not take in, for the
            // reason it outranks the body's: where the walk could not reach into what the position
            // holds, a rule about what is inside is a second description of that same stop and the
            // first is the cause (issue #626).
            case StructuralInspection.Blocked blocked -> new Blocked(axis.path(), blocked.why());
            // And a rule about this position's own values that went unread is said ahead of what a
            // body's comparison came to, where both have something to say. Both are true of such a
            // position and one line is written: the rule on the declaration is the one whose being
            // read would give the position an axis, and a comparison relating it to another
            // position would divide it no way however well it were read. So the reason that names
            // a limit points at the limit, and the reason that names a shape is not reached.
            //
            // It outranks nothing else. This is not a division, so the position is still pending
            // whatever a body says; it is a rule the model states, so an absence may not follow.
            case StructuralInspection.Leaf _ -> axis.unread() == null ? new Leaf(axis.path())
                    : new Blocked(axis.path(), axis.unread());
            // A position with no evidence that was never read. Nothing about a model follows from
            // it — an answer here would be this compiler's state written down as what the model
            // divides, which is the sentence the whole protocol is against.
            case null -> throw new IllegalStateException(
                    "nothing was read at " + axis.path() + " and it has no evidence");
        };
    }

    /**
     * What the position comes to, once what the rules said about it is known.
     *
     * <p>The phase's answer and not one producer's. A {@code guard}'s comparison and a newtype's
     * invariant are two producers of one kind of evidence, and {@link BodyCutInspection} is what
     * came of asking them — which is why this takes one of those rather than a list of lines and a
     * reason beside it. What makes it the phase's answer is where it is produced, not this
     * signature: a caller inside this package can still build one out of half a reading.
     *
     * <p>The structural reason outranks the rules'. Where the walk could not reach into what a
     * position holds, a rule naming something inside it describes that same stop from the other end
     * and the first is the cause (issue #626). So a {@link Blocked} completes as itself whatever
     * the rules came to, and only a {@link Leaf} can reach an absence.
     */
    default UndividedPosition complete(BodyCutInspection body) {
        if (body instanceof BodyCutInspection.Evidence) {
            // A line was drawn and the axis carrying it says it has none. Nothing a reader of a
            // model can act on: two readings of one position disagree about whether it has
            // evidence, and answering either way would report one of them as the model.
            throw new IllegalStateException(
                    "the rules drew a line at " + at() + " and its axis has no evidence");
        }
        return switch (this) {
            case Blocked blocked ->
                    UndividedPosition.cannotDerive(at(), ReportedReason.of(blocked.why()));
            case Leaf _ -> switch (body) {
                case BodyCutInspection.Blocked blocked ->
                        UndividedPosition.cannotDerive(at(), ReportedReason.of(blocked.why()));
                // The producers of both phases asked, none of them stopped, and none of them found
                // anything. Which is the only way to an absence, and is what one means: what those
                // readers read, rather than a claim about what could have been written.
                case BodyCutInspection.Exhausted _ -> UndividedPosition.absentAfter(this);
                case BodyCutInspection.Evidence _ -> throw new IllegalStateException("unreachable");
            };
        };
    }
}
