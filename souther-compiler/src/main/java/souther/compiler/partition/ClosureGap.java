package souther.compiler.partition;

import souther.compiler.check.RuleCitation;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.inputs.StandingQuestion;
import souther.compiler.observe.RunSensitivity;

import java.util.HashSet;
import java.util.Set;

/**
 * One thing that stopped a measure's reading of the model from running out.
 *
 * <p>What {@link MeasureClosure} used to answer with a boolean. Whether the reading ran out and what
 * was left of it when it did not are one question asked twice, and only the first of them had a
 * value: a measure that came back weaker than complete said so and nothing said why, so every reader
 * that wanted the why rebuilt it from the lists kept beside the measure (issue #953).
 *
 * <p><b>The fact itself, not a code and a name for what it is about.</b> Each arm holds what the
 * reader that found it produced. Written as a code and a subject the two would have to be taken
 * apart again by whoever wanted the rule, and a subject wide enough to hold a rule, a position and
 * an omitted axis is one every reader has to guess the shape of.
 *
 * <p>Which measures each of these costs is not asked here. That is
 * {@link MeasureClosure#of}'s to decide and the answers differ — a rule relating two positions
 * leaves neither measure short, and an omitted axis leaves the border measure short only where it
 * was carrying a line.
 */
public sealed interface ClosureGap {

    /**
     * Whether a run of this compiler that allows more could come to a different answer here.
     *
     * <p>Delegated and never decided. Three of the four hold what stopped them, so they ask it; the
     * fourth holds no reason on purpose and answers from what can reach it, which
     * {@code WhatEachClosureGapSaysAboutAWiderRunTest} holds to the reasons that do.
     */
    RunSensitivity runSensitivity();

    /**
     * What tells one of these from another.
     *
     * <p>The value itself, wherever everything the arm holds is what a reader is told. Where the
     * arm holds what evidenced the fact as well — the handle a reader is sent to, what a reading
     * was short of — the fact alone, so that one thing that went wrong, found twice, is one thing.
     *
     * <p>Asked of the arm and not written down by whoever gathers these. Two places put these
     * together — what one measure's reading came to, and what a measurement went without — and a
     * quotient written at each would be two answers to the question of what one gap is.
     */
    Object fact();

    /**
     * Two of these under one fact, as one, with what evidenced them accumulated.
     *
     * <p>Commutative, so which of the two a walk met first decides nothing about the result. A
     * {@code switch} with no {@code default}, so an arm added later has to say whether it carries
     * anything to accumulate before anything can put two of them together.
     */
    static ClosureGap merged(ClosureGap had, ClosureGap also) {
        return switch (had) {
            case RuleUnread it -> it.mergedWith(it.andAlso(also));
            case QuestionUnanswered it -> it.mergedWith(it.andAlso(also));
            // Equal under the fact and holding nothing else, so both are the same value.
            case RulesNotReached _, PositionNotReachedInto _ -> had;
        };
    }

    /**
     * A rule of the model a reader stopped on. The rule says which measures that costs
     * ({@link BlockReason.RuleWithoutLineReason#leavesShort}).
     *
     * <p>Only a rule this compiler got partway through. A rule read from end to end that draws no
     * line leaves no measure short of anything — that is what its half of the reasons answers, for
     * every one of them and not case by case — so it is not a gap in what was measured and there is
     * nothing here for it to be counted as. `MeasureClosure` asks the reason before building one of
     * these, and this refuses what that question would have had to let through.
     */
    record RuleUnread(RuleWithoutALine.Fact rule, Set<RuleCitation> cited) implements ClosureGap {

        public RuleUnread {
            if (!(rule.why() instanceof BlockReason.RuleReadingStopped)) {
                throw new IllegalArgumentException(
                        "a rule read to the end leaves no measure short: " + rule.why());
            }
            cited = cited == null ? Set.of() : Set.copyOf(cited);
        }

        /** One reader's finding, as that reader produced it: the rule it stopped on, and the handle
         *  it would send somebody to. */
        public static RuleUnread of(RuleWithoutALine found) {
            return new RuleUnread(found.fact(), Set.of(found.cited()));
        }

        /** The rule, the position and the limit. The handle is how a reader finds it and not what
         *  tells it from another. */
        @Override
        public Object fact() {
            return rule;
        }

        /** The other one, where it really is one of these. Two gaps filed under one fact and not
         *  of one kind is a fact two arms answer with, which nothing here can put together. */
        RuleUnread andAlso(ClosureGap other) {
            if (other instanceof RuleUnread it) {
                return it;
            }
            throw new IllegalArgumentException("a rule with no line and " + other
                    + " are filed under one fact");
        }

        /** Both readers' findings, as one: the rule, with every handle either of them offered. */
        public RuleUnread mergedWith(RuleUnread other) {
            Set<RuleCitation> both = new HashSet<>(cited);
            both.addAll(other.cited);
            return new RuleUnread(rule, both);
        }

        /** The rule's own answer, which the constructor above has already made sure there is one
         *  of: only a reading that stopped is admitted here, and a stop answers this. */
        @Override
        public RunSensitivity runSensitivity() {
            return ((BlockReason.RuleReadingStopped) rule.why()).runSensitivity();
        }
    }

    /**
     * A question the rules written about one position raise that nothing answered.
     *
     * <p>A clause's, and never a comparison's. A comparison raises a question exactly where the
     * reading of it reached a line, and that line is the answer — so a comparison either yields
     * both or yields neither and records what stopped its reading. Which is why a comparison's
     * incompleteness reaches this only as {@link RuleUnread}.
     */
    record QuestionUnanswered(StandingQuestion.Fact question, Set<RuleCitation> cited,
                              Set<BlockReason.AboutARule> stopped) implements ClosureGap {

        public QuestionUnanswered {
            cited = cited == null ? Set.of() : Set.copyOf(cited);
            stopped = stopped == null ? Set.of() : Set.copyOf(stopped);
            if (stopped.isEmpty()) {
                throw new IllegalArgumentException(
                        "a question stands because something was short of it");
            }
        }

        /**
         * One reading's account of it: the question, the handle for the rule that raised it, and
         * what that reading was short of.
         *
         * <p>What it was short of arrives as a set. A question stands until every reason it stands
         * for is gone, so the reasons are what a reader has to see away and neither how many parts
         * met one nor which part was read first is any of that.
         */
        public static QuestionUnanswered of(StandingQuestion asked) {
            return new QuestionUnanswered(asked.fact(), Set.of(asked.cited()),
                    Set.copyOf(asked.stopped()));
        }

        /** Which rule raised it and what it asks. What a reading was short of is why it stands
         *  rather than which question it is. */
        @Override
        public Object fact() {
            return question;
        }

        /** The other one, where it really is one of these, for the reason {@link RuleUnread}
         *  gives. */
        QuestionUnanswered andAlso(ClosureGap other) {
            if (other instanceof QuestionUnanswered it) {
                return it;
            }
            throw new IllegalArgumentException("a question that stands and " + other
                    + " are filed under one fact");
        }

        /** Both readings' accounts, as one: the question, with every handle and everything either
         *  of them was short of. */
        public QuestionUnanswered mergedWith(QuestionUnanswered other) {
            Set<RuleCitation> handles = new HashSet<>(cited);
            handles.addAll(other.cited);
            Set<BlockReason.AboutARule> met = new HashSet<>(stopped);
            met.addAll(other.stopped);
            return new QuestionUnanswered(question, handles, met);
        }

        /**
         * What the reasons the question is short for come to, and it takes all of them.
         *
         * <p>A question stands until every reason it stands for is gone, so a run that allows more
         * answers it only where every one of those is a stop such a run gets past. Read as "one of
         * them was", a question short for a figure and for a form nothing reads would send a person
         * to allow more and leave the form exactly as unread.
         *
         * <p>Empty is {@link RunSensitivity#UNAFFECTED} for the same
         * reason it is not {@code MAY_CHANGE}: nothing here is a figure a run may allow more of.
         */
        @Override
        public RunSensitivity runSensitivity() {
            return stopped.stream()
                    .allMatch(each -> each.runSensitivity()
                            == RunSensitivity.MAY_CHANGE)
                    ? RunSensitivity.MAY_CHANGE
                    : RunSensitivity.UNAFFECTED;
        }
    }

    /**
     * A position whose rules nothing enumerated. It raises no question, so it cannot be short of
     * one — which is why it is a gap of its own and not one of the two above.
     *
     * <p><b>Not every way the rules go unread reaches this.</b> A handing over left standing because
     * the walk could not go into the position is the same stop {@link PositionNotReachedInto}
     * reports, and it is written there once. Which of the ways this is comes off the arm the reading
     * settled and never off what else was found at the path
     * ({@link souther.compiler.inputs.RulesLeftUnread}): a position the reading entered and lost a
     * clause of its own is an independent finding, and a fold on the path would take it with the
     * other (issue #1084).
     *
     * <p><b>And two of those ways reach a document as this one word.</b> A reading that lost a
     * clause of its own and a recipient that got no reading are different causes and both are
     * things an author is told about; what they are told is that the rules at this position were
     * not all reached, which is what this says. The reason stays inside
     * ({@link souther.compiler.inputs.RulesLeftUnread}) because a document naming it would make a
     * change to how this compiler traverses a model into a change to what its documents carry. Two
     * of these at one position are one entry, which is that sentence said once.
     *
     * <p><b>And whose position it is.</b> An account of one behavior is put together with another's
     * — a module's is the union of them — and a union keeps one of two equal facts. Two behaviors
     * taking one type have positions spelled alike, so without the behavior the second of them
     * would be the first said again.
     */
    record RulesNotReached(String behavior, souther.compiler.inputs.PositionId at)
            implements ClosureGap {

        /**
         * The one arm that answers rather than asks, because it holds no reason to ask.
         *
         * <p>What reaches it is a {@link souther.compiler.inputs.RulesLeftUnread}: a clause this
         * reading lost, and a handing over nobody took over. Neither is a figure this compiler
         * compared anything against, so a run that allows more meets both again — and the reason
         * stays inside for the reason given above, which is that a document naming it would make a
         * change to how this compiler traverses a model into a change to what its documents carry.
         *
         * <p>Said here and held elsewhere. A third way of leaving rules unread that a wider run
         * does get past would make this answer wrong with nothing in this file to say so, so
         * {@code WhatEachClosureGapSaysAboutAWiderRunTest} asks every arm of that type.
         */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }

        /** Everything it holds is what a reader is told: whose position, and which. */
        @Override
        public Object fact() {
            return this;
        }
    }

    /**
     * A position the walk could not reach into, with what the structural reading found instead.
     *
     * <p>The one arm for a position with no rule to name. There were two for a while — this and a
     * {@code PositionBlocked} taking {@code PositionReadingBlocked}, which is the same fact keyed by
     * path rather than by axis. It was written from the list {@code PartitionEvidence} keeps beside
     * the measures rather than from what {@link MeasureClosure#of} finds, so nothing ever built one:
     * an arm taken from a second representation of a fact, which is the mistake #953 is about, in
     * miniature.
     *
     * <p><b>{@code at} names the position, and not a number measured of it.</b> A location is
     * measured at as many numbers as the rules name of it, and one stop under the location is one
     * thing that went wrong however many of those there are. Named for a measure, it is one entry
     * per number and no reader can tell that from several stops. What weakens one measurement is
     * said per measurement elsewhere; these are one behavior's account of what its reading of the
     * model came to, and a reader holding a measure reaches its position by the path it reads from.
     *
     * <p>{@link RulesNotReached} is keyed the same way, so the two are one vocabulary, and both
     * carry whose position it is for the reason given there.
     *
     * <p>Written from {@link souther.compiler.inputs.BlockedDescent} and never from what the axis is
     * still waiting on. A position something answered for keeps no continuation, and was still never
     * entered.
     */
    record PositionNotReachedInto(String behavior, souther.compiler.inputs.PositionId at,
                                  BlockReason.AboutThePosition why) implements ClosureGap {

        /** The stop's own answer. */
        @Override
        public RunSensitivity runSensitivity() {
            return why.runSensitivity();
        }

        /** Everything it holds is what a reader is told: whose position, which, and what the walk
         *  met there. */
        @Override
        public Object fact() {
            return this;
        }
    }
}
