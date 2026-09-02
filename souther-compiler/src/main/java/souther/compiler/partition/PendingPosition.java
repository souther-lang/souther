package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;
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
     *
     * <p>About the position and never about a rule. What stopped here is a walk that did not arrive
     * at the rules, so there is none to name — a stop a reading of a rule recorded is that rule's
     * finding, and this arm is the one a report writes at a position.
     */
    record Blocked(TermPath at, BlockReason.AboutThePosition why) implements PendingPosition {}

    /**
     * The rules of the position raise a question nothing answered.
     *
     * <p>Its own state beside {@link Blocked}, which is the walk not having reached the position at
     * all. What they share is that nothing about the model follows from there being no class here;
     * what they do not share is where the fact is made — a question stands because no reading of
     * the rule that raised it took the rule in, and which reading was short of it is this
     * compiler's business rather than the question's.
     */
    record AQuestionStands(TermPath at) implements PendingPosition {}

    /**
     * What is still to be answered for at {@code at}, or null where something measures it.
     *
     * <p>Null and not a case, because a position something measures is not pending anything: the
     * question this type is about does not arise for it. Which is also why {@link #complete}
     * refuses a body that says it drew a line — two readings would then disagree about whether this
     * position has evidence.
     *
     * <p><b>Asked of the position and of whether anything measures it, and not through a measure.</b>
     * A location is measured at as many numbers as the rules name of it, so a caller with a measure
     * in hand has one of several and the question is not about any of them. Asked through one, a
     * location divided at one of its numbers and not at another was answered by whichever measure
     * the caller happened to hold.
     */
    static PendingPosition of(PositionAccount at, boolean measured) {
        if (measured) {
            return null;
        }
        // A position with no evidence and no fallback was never read. Nothing about a model follows
        // from it — an answer here would be this compiler's state written down as what the model
        // divides, which is the sentence the whole protocol is against.
        if (at.pending() == null) {
            throw new IllegalStateException(
                    "nothing was read at " + at.path() + " and it has no evidence");
        }
        // The reading not having got to the rules of the position outranks what those rules raise:
        // a question about a rule nothing arrived at is a second description of that same hole, and
        // the first is the cause. Which of the ways that happened is the position's own answer
        // ({@link PositionAccount#notReachedInto}) and is not worked out again here.
        souther.compiler.inputs.BlockReason.AboutThePosition unreached = at.notReachedInto();
        if (unreached != null) {
            return new Blocked(at.path(), unreached);
        }
        // And where it did get to them, what the position is waiting on is whatever those rules
        // raise that nothing answered. What the walk found under the position is no part of it: an
        // element or a case is a position of its own, and what is written about it is answered
        // there rather than being this position's to be short of.
        return pending(at);
    }

    /**
     * A position nothing under it accounts for, in the state its questions put it in.
     *
     * <p>The accounting's answer and not this reader's. A question stands where no reading took the
     * rule that raised it in, so a reading short of a rule another one read leaves nothing here —
     * which is what a completeness read off one reading's own set could not say.
     */
    private static PendingPosition pending(PositionAccount at) {
        return at.standing().isEmpty() ? new Leaf(at.path()) : new AQuestionStands(at.path());
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
     * <p>Null for the other two states. A question that stands is a finding about the rule that
     * raised it, made where the rule is known and naming it; nothing stopped at a {@link Leaf}, so
     * there is nothing to be waiting on. Neither has a stop about the position for this to report,
     * which is what this one is.
     */
    default souther.compiler.inputs.PositionReadingBlocked reportable() {
        if (!(this instanceof Blocked blocked)) {
            return null;
        }
        return new souther.compiler.inputs.PositionReadingBlocked(at(), blocked.why());
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
     * <p><b>A projection of two accounts, and neither of them is a reading's own reach.</b> Whether
     * the walk reached into the position is the structural reading's, and whether a question its
     * rules raise is standing is the accounting's — asked of every reading at once, so a rule one
     * of them was short of and another took in leaves nothing standing. Decided from what a single
     * reading was left with instead, a rule read to the end by the reading of ends and left by the
     * reading of values came out as a position nothing could read, over an accounting that had
     * already answered every question about it.
     *
     * <p>The structural stop comes first for the reason it always did: where the walk could not
     * reach into what the position holds, what is written under it is whatever it is, and a
     * question about it is a second description of that same stop.
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
            // Nothing about the model follows from there being no class: the position was not read
            // into, or a rule of it raises a question nothing answered.
            case Blocked _, AQuestionStands _ -> UndividedPosition.cannotDerive(at());
            case Leaf _ -> stated(body) ? UndividedPosition.statedWithoutALine(at())
                    : UndividedPosition.absentAfter(this);
        };
    }

    /**
     * Whether the model states something at this position that came to no line.
     *
     * <p>The rules of the position and the rules a body writes about it are one question here: a
     * position either has a rule filed at it or it has none, and a verdict saying the model divides
     * it no way would deny whichever of them is written. Which rule that is, and what became of the
     * reading of it, are said in the finding that names it.
     */
    private static boolean stated(BodyCutInspection body) {
        return switch (body) {
            // The producers of this phase asked, none of them found anything, and no rule is filed
            // at the position. Which is what an absence means: what those readers read, rather than
            // a claim about what could have been written.
            case BodyCutInspection.Exhausted _ -> false;
            case BodyCutInspection.ARuleWithNoLine _ -> true;
            case BodyCutInspection.Evidence _ -> throw new IllegalStateException("unreachable");
        };
    }
}
