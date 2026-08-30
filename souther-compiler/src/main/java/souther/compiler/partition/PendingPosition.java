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
    record Blocked(TermPath at, BlockReason.ReadingStopReason why) implements PendingPosition {}

    /**
     * A rule states something here and the readings turn it into no line, every one of them having
     * run to the end.
     *
     * <p>Its own state beside {@link Blocked}, which is this compiler having fallen short. Nothing
     * is missing here: the rule relates the position to another, or cuts a quantity it does not
     * appear in, or draws its line where that quantity never runs. What the two share is that an
     * absence may not follow from either — the model states something at this position — and what
     * they do not share is whose work it would be to change that.
     *
     * <p>Held apart because the consumers of this chain each carry the same distinction and each
     * used to read it off which state this was. A rule read from end to end arriving as
     * {@link Blocked} came out as a position this compiler could not read, in a verdict, in a
     * generation's account of why no row could answer, and in the words a claim is annotated with.
     */
    record ARuleWithNoLine(TermPath at, BlockReason.ReadToEndWithoutLine why)
            implements PendingPosition {}

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
        return switch (at.pending()) {
            // The structural stop outranks a rule the local reading could not take in, for the
            // reason it outranks the body's: where the walk could not reach into what the position
            // holds, a rule about what is inside is a second description of that same stop and the
            // first is the cause (issue #626).
            case StructuralInspection.Continuation.Blocked blocked ->
                    new Blocked(at.path(), blocked.why());
            // And a rule about this position's own values that went unread is said ahead of what a
            // body's comparison came to, where both have something to say. Both are true of such a
            // position and one line is written: the rule on the declaration is the one whose being
            // read would give the position an axis, and a comparison relating it to another
            // position would divide it no way however well it were read. So the reason that names
            // a limit points at the limit, and the reason that names a shape is not reached.
            //
            // It outranks nothing else. This is not a division, so the position is still pending
            // whatever a body says; it is a rule the model states, so an absence may not follow.
            case StructuralInspection.Continuation.None _ -> pending(at);
            // A sequence, whose elements were reached and are a position of their own. Nothing
            // stopped here, so this is the same state a leaf is in: what the list itself divides
            // into is what its own rules say about how many it holds, and an absence may follow
            // where they say nothing. What is written about what it holds is answered at the
            // element and is not this position's to be short of.
            case StructuralInspection.Continuation.Elements _,
            // And a sum, whose cases were reached and stand under it. Nothing stopped here either:
            // a sum with no evidence is one whose own cases the rules left it none of, which is a
            // reading that ran to the end.
                 StructuralInspection.Continuation.Branches _ -> pending(at);
            // A position with no evidence that was never read. Nothing about a model follows from
            // it — an answer here would be this compiler's state written down as what the model
            // divides, which is the sentence the whole protocol is against.
            case null -> throw new IllegalStateException(
                    "nothing was read at " + at.path() + " and it has no evidence");
        };
    }

    /**
     * A position nothing under it accounts for, in the state whatever is left at it puts it in.
     *
     * <p>Which of the two states is the evidence's answer and not this reader's. Read off whether
     * the slot was filled at all, a rule read from end to end put the position in the state that
     * says this compiler could not read it.
     */
    private static PendingPosition pending(PositionAccount at) {
        return switch (at.leftWith()) {
            case null -> new Leaf(at.path());
            case LeftAtThePosition.AReadingStopped(var why) -> new Blocked(at.path(), why);
            case LeftAtThePosition.ARuleWithNoLine(var why) ->
                    new ARuleWithNoLine(at.path(), why);
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
     * could not use, which is an {@link souther.compiler.inputs.RuleWithoutALine} made by the reader that
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
            // A rule this got partway through is a finding about that rule, made where the rule is
            // known and named there. What is written here is the other one: a position whose rules
            // this never arrived at, which names no rule because none was seen.
            case BlockReason.RuleReadingStopped _ -> null;
            // And an answer nobody could work out is not written here either, for the reason the
            // one above is not: what is reported here names a rule or names a position whose rules
            // were never reached, and this is neither. It qualifies what the classes are and is
            // carried with them ({@code AdmissibleSet.Widening}), where a reader meets it beside
            // the values it is about rather than as a rule that was never read.
            case BlockReason.AnswerRealizationStopped _ -> null;
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
     * <p><b>Two readings answer about one position, and the verdict is one.</b> Which of their
     * answers outranks is {@link LeftAtThePosition#outranking}'s and is written once: a reading
     * that stopped over a rule read to the end, and either over nothing being stated. Decided per
     * phase instead, the phases disagreed — a rule read to the end in the declaration hid a stop
     * in the body, and a rule read to the end in the body was reported as a stop because that is
     * the only thing the body could say.
     *
     * <p>The structural reason is among what outranks, not beside it. Where the walk could not
     * reach into what a position holds, a rule naming something inside it describes that same stop
     * from the other end and the first is the cause (issue #626) — a stop either way, so the
     * priority already has it.
     */
    default UndividedPosition complete(BodyCutInspection body) {
        if (body instanceof BodyCutInspection.Evidence) {
            // A line was drawn and the axis carrying it says it has none. Nothing a reader of a
            // model can act on: two readings of one position disagree about whether it has
            // evidence, and answering either way would report one of them as the model.
            throw new IllegalStateException(
                    "the rules drew a line at " + at() + " and its axis has no evidence");
        }
        LeftAtThePosition left = LeftAtThePosition.outranking(leftHere(), leftBy(body));
        return switch (left) {
            case null -> UndividedPosition.absentAfter(this);
            // Something is written here and this compiler did not read it, so nothing about the
            // model follows from there being no line.
            case LeftAtThePosition.AReadingStopped _ -> UndividedPosition.cannotDerive(at());
            // Read to the end, and what it says draws no line. Not a derivation this compiler could
            // not make, and not an absence either: the model states something at this position, and
            // the rule that states it is named in a finding of its own.
            case LeftAtThePosition.ARuleWithNoLine _ -> UndividedPosition.statedWithoutALine(at());
        };
    }

    /** What the reading of this position's own declarations left it with. */
    private LeftAtThePosition leftHere() {
        return switch (this) {
            case Leaf _ -> null;
            case Blocked blocked -> new LeftAtThePosition.AReadingStopped(blocked.why());
            case ARuleWithNoLine it -> new LeftAtThePosition.ARuleWithNoLine(it.why());
        };
    }

    /** And what the reading of the body left it with. */
    private static LeftAtThePosition leftBy(BodyCutInspection body) {
        return switch (body) {
            // The producers of this phase asked, none of them stopped, and none of them found
            // anything. Which is one half of the way to an absence, and is what it means: what
            // those readers read, rather than a claim about what could have been written.
            case BodyCutInspection.Exhausted _ -> null;
            case BodyCutInspection.NoLine(var left) -> left;
            case BodyCutInspection.Evidence _ -> throw new IllegalStateException("unreachable");
        };
    }
}
