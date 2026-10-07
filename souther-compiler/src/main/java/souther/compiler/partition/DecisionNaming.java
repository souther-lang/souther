package souther.compiler.partition;

import souther.compiler.check.Choice;
import souther.compiler.check.Comparison;
import souther.compiler.check.ScopeStep;
import souther.compiler.core.Core;
import souther.compiler.flow.Arrival;
import souther.compiler.flow.Naming;
import souther.compiler.flow.Truth;
import souther.compiler.flow.WhatAConditionRuns;
import souther.compiler.inputs.InputReads;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * How the decision a body states writes down what got a run to an answer.
 *
 * <p>The reader-specific half of {@link souther.compiler.flow.ValueArrivals}. What the ways through
 * a body are is the body's own answer and is computed with no naming at all; which distinctions each
 * way turns on, and what tells one from another, is this.
 *
 * <p><b>Its own naming beside the one the combinations use.</b> That one writes a way as a class of
 * one position and tells two readings of one proposition apart by where each is written, which is
 * right for a reading whose places are run-time events. A decision rule is told apart by the
 * proposition: two writings of one inequality are one column, and a table with a column apiece
 * admits an assignment where a proposition holds and does not.
 *
 * <p><b>A condition this has no words for is a column and not a silence.</b> Answering null would
 * leave the way carrying every other condition and saying nothing about this one, which reads as a
 * rule that turns on less than it does. So a shape the arithmetic cannot state comes back as a
 * column the reading admits it cannot say the meaning of, and the way stays whole.
 *
 * <p>What does answer null is a fork whose ways could not all be written down. There is no condition
 * there to name — the reading fell short of enumerating them — so the way is
 * {@link souther.compiler.flow.Completeness#PARTIAL}, which is what a measurement that could not be
 * made in full says of itself.
 */
final class DecisionNaming implements Naming<DecisionPath> {

    /**
     * What a condition of this body decides, made once beside the walk.
     *
     * <p>Not held as the reading of the input itself. This value is at a program point the way the
     * environment is, so a reading kept in it would be copied into every step and asked of whichever
     * copy a reader holds.
     */
    private final DecisionMeanings meanings;

    private final InputReads reads;

    /**
     * The names the conditions of this reading go by, shared down every scope.
     *
     * <p>One register for the body, because a condition met under a binding and the same condition
     * met outside it are one condition. A register per scope would name it once per scope, and two
     * accounts of one condition agree about nothing.
     */
    private final ConditionNumbering numbering;

    private final int mostArrivals;

    DecisionNaming(DecisionMeanings meanings, InputReads reads, ConditionNumbering numbering,
                   int mostArrivals) {
        this.meanings = meanings;
        this.reads = reads;
        this.numbering = numbering;
        this.mostArrivals = mostArrivals;
    }

    @Override
    public DecisionPath nowhere() {
        return DecisionPath.NOWHERE;
    }

    @Override
    public DecisionPath join(DecisionPath held, DecisionPath more) {
        return held.and(more);
    }

    @Override
    public Naming<DecisionPath> entering(ScopeStep step) {
        InputReads inside =
                reads.entering(step, meanings.states().symbols(), meanings.states().newtypes());
        return inside == reads ? this
                : new DecisionNaming(meanings, inside, numbering, mostArrivals);
    }

    /**
     * That {@code value} came out {@code held}, as the distinction the body draws by it.
     *
     * <p>Read through {@link Condition}, which is the one reading of what a boolean subtree of a
     * body means, and turned into what it states by {@link ReachingCuts#stating} — the same
     * arithmetic every other reader of a comparison takes, so a line drawn on one and a column here
     * cannot come apart.
     *
     * <p>The connectives are not reached here: the reading of the ways settles an operator that
     * stops when its answer is settled, which is what puts the short-circuit in the rules. What
     * arrives is one condition, and what comes back is the columns it states.
     */
    @Override
    public DecisionPath side(Core value, boolean held) {
        Condition condition = Condition.of(value, reads, meanings.states().symbols(),
                meanings.states().newtypes(), numbering);
        List<DecisionMeanings.Read> decided = meanings.deciding(condition, held);
        // A side the reading of the ways let through and this reading sees no row take. Both ask
        // which answers a value can give of the same reading, so they part only where it was read
        // under different names — and then this naming has no words for the side, which is what
        // null is ({@link Naming#side}): the way stays, short of whole, and is not dropped on the
        // word of one of two readings that disagree.
        if (decided == null) {
            return null;
        }
        DecisionPath path = DecisionPath.NOWHERE;
        for (DecisionMeanings.Read each : decided) {
            path = path.and(each.answer(), shownBy(each.answer(), condition, held),
                    each.onTheWay());
            if (path == null) {
                return null;
            }
        }
        return path;
    }

    @Override
    public DecisionPath matchCase(Core.Match match, int part) {
        // Nothing, for an arm every row at the fork takes, which decides nothing.
        return meanings.entering(match, part, reads, numbering)
                .map(read -> atAnArm(read, match.occurrence(), part))
                .orElse(DecisionPath.NOWHERE);
    }

    /**
     * The distinction the arm is an answer of.
     *
     * <p>For an {@code if}, the fork's own condition coming out the way this arm is under. Asked
     * where the ways the condition comes out could not all be written down, which is what a
     * condition whose value this reading cannot work out leaves — a call to one of the language's
     * own operations among them. The fork is still one distinction with two answers, and the arms
     * are those answers: run together they would report a distinction the body draws as one it does
     * not, and both arms would carry the same empty path. The same condition the reading would have
     * named had it been able to value it, which is why it is asked for the same way: a column
     * minted here instead would be a second name for one condition, and the two accounts of it would
     * agree about nothing.
     *
     * <p>Seen at the arm. Whatever the condition coming out that way states, a run down the arm is
     * a run that brought it out that way, so a column of it nothing else records is seen there —
     * the way {@link #seenAtTheArm} sees a way the condition's ways could be written down as.
     *
     * <p>For an attempt, the arm itself. Whether the invariant held is a condition no expression of
     * the body states, so there is no condition to ask for; the arm is a column this reading names
     * and says it cannot read, and a run through it is seen at the arm the way a run through a case
     * of a {@code match} is.
     */
    @Override
    public DecisionPath forkArm(Core fork, int part) {
        return switch (Choice.decidingArm(fork, part)) {
            case Choice.Decides.ACondition(Core.If iff, boolean holding) -> {
                DecisionPath stated = side(iff.cond(), holding);
                yield stated == null ? null : atTheArm(iff, part, stated);
            }
            case Choice.Decides.ItWasBuilt(Core.IfConstructed attempt) -> atAnArm(
                    meanings.attempting(attempt, part, attempt.then().pos(), numbering),
                    attempt.occurrence(), part);
            case Choice.Decides.ItDeparted(Core.IfConstructed attempt, Core.ElseArm on) -> atAnArm(
                    meanings.attempting(attempt, part, on.body().pos(), numbering),
                    attempt.occurrence(), part);
            // Named by matchCase, which is asked of the match and not of a fork in general.
            case Choice.Decides.ACase _ -> throw new IllegalStateException(
                    "a case of a match at " + fork.pos() + " was asked of as an arm of a fork");
            case Choice.Decides.ByArgumentRelations _ -> throw new IllegalStateException(
                    "an operation the library defines by cases at " + fork.pos()
                            + " was asked of as an arm of a fork, and no walk enters one");
        };
    }

    /**
     * The way, with each condition on it that nothing records seen at the arm.
     *
     * <p>A truth the body was handed is a column this reading states in full and no construct of
     * the model answers, so a rule through it is one no run is recognised at — until the fork that
     * takes it is one the way is the only way into. A run at the arm then took the way, and so
     * every condition on it came out the way the rule says.
     *
     * <p>A way whose value the reading could not work out says nothing of the condition, and the
     * condition coming out the arm's way is put on it: the column {@link #forkArm} names, which is
     * the one the arm is taken on.
     *
     * <p>Nothing, for a way this reading could not write down whole: the column it has no words for
     * is not on the path, and the arm would be seen standing for a rule that turns on less than the
     * way does. And the way as it is, for a fork the model does not state — one inside the
     * language's own operations has no arm a run is recorded at.
     */
    @Override
    public DecisionPath seenAtTheArm(Core.If fork, int part, Arrival<DecisionPath> onlyWay) {
        if (!onlyWay.isComplete()) {
            return null;
        }
        DecisionPath way = onlyWay.path();
        if (onlyWay.value() == Truth.UNREAD) {
            DecisionPath stated = side(fork.cond(), part == 0);
            way = stated == null ? null : way.and(stated);
        }
        return way == null ? null : atTheArm(fork, part, way);
    }

    /**
     * The way, with each condition settled short of an operand seen at the arm taken without that
     * operand having run — where every run down the arm ran the operator.
     *
     * <p>Only then does a run down the arm that did not reach the operand say the left settled.
     * Under {@code x > 0 && (flag && n > 0)} the inner {@code &&} runs only where {@code x > 0}
     * held, and a run down the {@code else} arm with {@code n > 0} not run may have stopped at
     * {@code x > 0} and never asked {@code flag}.
     */
    @Override
    public DecisionPath oneOfTheWaysIn(Core.If fork, int part, DecisionPath way) {
        ModelOccurrence stated = forkStated(fork);
        if (stated == null) {
            return way;
        }
        Set<ModelOccurrence> alwaysRun = new LinkedHashSet<>();
        for (Core.Binary ran : WhatAConditionRuns.whenItCameOut(fork.cond(), part == 0)
                .operators()) {
            recordedAsItself(ran.right()).ifPresent(alwaysRun::add);
        }
        return way.seenAgain(shown -> shown instanceof ShownBy.ShortOf(var _, var notReached)
                && alwaysRun.contains(notReached)
                ? new ShownBy.AtAnArmShortOf(stated, part, notReached) : shown);
    }

    /**
     * The left's one way of going on, with what nothing records on it seen where the right is: a
     * run recorded at the right ran it, which is what the left going on is.
     *
     * <p>Only where the right is itself the construct a run through it is recorded at. A right that
     * is a name for a truth worked out before the operator ran is recorded where it was worked out,
     * whichever way the left came out.
     */
    @Override
    public DecisionPath wentOn(Core.Binary operator, DecisionPath left,
                               Arrival<DecisionPath> right) {
        Optional<ModelOccurrence> recorded = recordedAsItself(operator.right());
        if (recorded.isEmpty() || right.value() == Truth.UNREAD) {
            return left;
        }
        ShownBy seen = new ShownBy.AtAnOutcome(recorded.get(), right.value() == Truth.TRUE);
        return left.seenAgain(shown -> switch (shown) {
            case ShownBy.NothingIsRecorded _, ShownBy.ShortOf _ -> seen;
            case ShownBy.AtAnOutcome _, ShownBy.AtAnArm _, ShownBy.AtAnArmShortOf _ -> shown;
        });
    }

    /**
     * The left's one way of settling the answer, with what nothing records on it said to have been
     * settled short of the right — which a fork whose condition always runs the operator turns
     * into a place to be seen at ({@link #oneOfTheWaysIn}).
     *
     * <p>A condition already settled short of an operand further in keeps that one: the operand
     * nearest it is the one whose not having run says how it came out.
     */
    @Override
    public DecisionPath stoppedShort(Core.Binary operator, DecisionPath left) {
        Optional<ModelOccurrence> recorded = recordedAsItself(operator.right());
        if (recorded.isEmpty()) {
            return left;
        }
        return left.seenAgain(shown -> shown instanceof ShownBy.NothingIsRecorded(var condition)
                ? new ShownBy.ShortOf(condition, recorded.get()) : shown);
    }

    /**
     * {@code path} with every condition nothing records seen at arm {@code part} of {@code fork},
     * or as it is where the model states no such fork.
     *
     * <p>Every one of them, settled short of an operand or not: the path is the only way into the
     * arm, so the arm alone says each came out the way the path says.
     */
    private static DecisionPath atTheArm(Core.If fork, int part, DecisionPath path) {
        ModelOccurrence stated = forkStated(fork);
        if (stated == null) {
            return path;
        }
        ShownBy arm = new ShownBy.AtAnArm(stated, part);
        return path.seenAgain(shown -> switch (shown) {
            case ShownBy.NothingIsRecorded _, ShownBy.ShortOf _ -> arm;
            case ShownBy.AtAnOutcome _, ShownBy.AtAnArm _, ShownBy.AtAnArmShortOf _ -> shown;
        });
    }

    /** The fork of the model {@code fork} is, or null for one the model does not state — one inside
     *  the language's own operations, or one this compiler composed, which has no place at all. */
    private static ModelOccurrence forkStated(Core.If fork) {
        return Optional.ofNullable(fork.occurrence()).flatMap(ModelOccurrence::statedAt)
                .orElse(null);
    }

    /**
     * The construct of the model {@code value} itself is, where a run through it is recorded there:
     * a comparison, or an application of one of the language's operations, written where it stands
     * and not reached through a name.
     */
    private static Optional<ModelOccurrence> recordedAsItself(Core value) {
        return switch (Core.withoutStanding(value)) {
            case Core.Binary binary when Comparison.of(binary).isPresent()
                    && binary.occurrence() != null ->
                    ModelOccurrence.statedAt(binary.occurrence());
            case Core.PreservedCall applied when applied.occurrence().isWritten() ->
                    ModelOccurrence.statedAt(applied.occurrence());
            default -> Optional.empty();
        };
    }

    /**
     * A path through one arm of a fork, carrying {@code read} and seen at that arm of the model.
     *
     * <p>A fork no construct of the model states — one inside the language's own operations — has
     * no arm a run is recorded at, and says so rather than being left off the path.
     */
    private static DecisionPath atAnArm(DecisionMeanings.Read read, ConstructOccurrence fork,
                                        int part) {
        ModelOccurrence stated = ModelOccurrence.statedAt(fork).orElse(null);
        return DecisionPath.NOWHERE.and(read.answer(), stated == null
                ? new ShownBy.NothingIsRecorded(read.answer().condition())
                : new ShownBy.AtAnArm(stated, part), read.onTheWay());
    }

    @Override
    public int mostArrivals() {
        return mostArrivals;
    }

    /**
     * Where a run through one condition is recorded, said in the model's words.
     *
     * <p>The construct of the model that answers the truth, which is what the tree the rules are
     * read off and the tree that runs agree about: a comparison, or an application of one of the
     * language's operations. A condition with no such construct — a truth asked of a name the body
     * was handed — has none to be seen at, and says so rather than being left off the path.
     */
    private static ShownBy shownBy(DecidedCondition answer, Condition condition, boolean held) {
        Optional<ModelOccurrence> answered = answeredAt(condition);
        return answered.isPresent() ? new ShownBy.AtAnOutcome(answered.get(), held)
                : new ShownBy.NothingIsRecorded(answer.condition());
    }

    /** The construct of the model {@code condition}'s truth is answered by, where it is one. */
    static Optional<ModelOccurrence> answeredAt(Condition condition) {
        return switch (condition) {
            case Condition.Compares one -> one.states();
            case Condition.Truth truth -> recordedAsItself(truth.value());
            case Condition.Joined _ -> Optional.empty();
        };
    }
}
