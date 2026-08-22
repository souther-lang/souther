package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.StructuralInspection;
import souther.compiler.inputs.TermPath;

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
            // A sequence, whose elements were reached and are a position of their own. Nothing
            // stopped here, so this is the same state a leaf is in: what the list itself divides
            // into is what its own rules say about how many it holds, and an absence may follow
            // where they say nothing. What is written about what it holds is answered at the
            // element and is not this position's to be short of.
            case StructuralInspection.Inside _ -> axis.unread() == null ? new Leaf(axis.path())
                    : new Blocked(axis.path(), axis.unread());
            // A position with no evidence that was never read. Nothing about a model follows from
            // it — an answer here would be this compiler's state written down as what the model
            // divides, which is the sentence the whole protocol is against.
            case null -> throw new IllegalStateException(
                    "nothing was read at " + axis.path() + " and it has no evidence");
        };
    }

    /**
     * The finding this comes to, or null where there is none to make.
     *
     * <p>The resolution, and the only place a structural stop becomes something a report says. What
     * a producer records is a candidate: the walk could not reach into what a position holds, and
     * that is worth telling an author exactly when nothing else answered for the position. Reported
     * off the producer alone, {@code note: String?} said its values are held inside something this
     * does not reach into — true of the compiler, and no account of this position, whose two cases
     * the reading divided perfectly well. Reaching one of these is already the proof that nothing
     * did: {@link #of} refuses an axis with evidence.
     *
     * <p>Null where the surviving reason is about a rule. Such a reason is a rule this read and
     * could not use, which is an {@link souther.compiler.inputs.UnreadRule} made by the reader that
     * read it and carrying which rule — said again here, it would be the same fact twice, once
     * without the rule.
     *
     * <p>Null for a {@link Leaf} too: nothing stopped, so there is nothing to be waiting on.
     *
     * <p>Classified rather than filtered, and with no {@code default}. Asked as "is this about the
     * position", a reason that is neither this nor about a rule answers no and is dropped here with
     * nothing saying where it went instead — and only one of the two nulls above is proven, so the
     * question the filter asked was not the question being answered. Each of what a reason may be
     * answers for itself instead, and a stop added beside them stops the compile here.
     *
     * <p>What arrives here is why a derivation stopped, which is the whole of what a
     * {@link BlockReason} is. A reading that ran to the end of the rules and could not hold what
     * they say together stopped nothing and is not one of these at all: it is carried as a
     * qualification of the classes and reported on its own, so it is not a candidate this resolves
     * and there is nothing here for it to be misfiled as.
     */
    default souther.compiler.inputs.PositionReadingBlocked reportable() {
        if (!(this instanceof Blocked blocked)) {
            return null;
        }
        return switch (blocked.why()) {
            case BlockReason.AboutARule _ -> null;
            case BlockReason.AboutThePosition why ->
                    new souther.compiler.inputs.PositionReadingBlocked(at(), why);
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
            case Blocked _ -> UndividedPosition.cannotDerive(at());
            case Leaf _ -> switch (body) {
                case BodyCutInspection.Blocked _ -> UndividedPosition.cannotDerive(at());
                // The producers of both phases asked, none of them stopped, and none of them found
                // anything. Which is the only way to an absence, and is what one means: what those
                // readers read, rather than a claim about what could have been written.
                case BodyCutInspection.Exhausted _ -> UndividedPosition.absentAfter(this);
                case BodyCutInspection.Evidence _ -> throw new IllegalStateException("unreachable");
            };
        };
    }
}
