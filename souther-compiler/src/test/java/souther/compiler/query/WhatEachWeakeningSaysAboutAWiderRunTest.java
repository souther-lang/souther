package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.DecidedBy;
import souther.compiler.types.WrittenOwner;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PositionId;
import souther.compiler.inputs.RulesLeftUnread;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowRef;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.observe.WorkFigure;
import souther.compiler.source.SourceId;
import souther.compiler.partition.Border;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.Replacement;
import souther.compiler.partition.ClosureGap;
import souther.compiler.partition.ReadingGap;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every way a measurement is left weaker than it looks, and what each says about a wider run.
 *
 * <p>The seal refuses an arm nobody answered for: {@link Weakening#runSensitivity} is abstract, so
 * a twelfth arm does not compile until somebody writes an answer. What it cannot refuse is an arm
 * answering for itself where something further in already knows — which is the reconstruction this
 * whole type exists to stop, and it would be as invisible here as it was there.
 *
 * <p>So the rows say which arms decide and which pass the question on. An arm that holds what
 * stopped it must ask that thing, and only an arm that is the first place the fact exists may
 * answer. A row moved from {@code asks} to {@code answers} is somebody deciding to hold a second
 * copy of a fact, and this is where they have to write it down.
 */
class WhatEachWeakeningSaysAboutAWiderRunTest {

    /**
     * Every arm, and what it comes to.
     *
     * <p>Written as {@code answers|asks <what>/sensitivity}: whether the arm is the first place the
     * fact exists or hands the question further in, and what the arm below then says.
     */
    private static Map<String, String> theWeakenings() {
        Map<String, String> table = new LinkedHashMap<>();
        // The four that hold what stopped them. Each is the reason this type is a sum rather than a
        // code and a subject: what the reader that found it produced travels whole, so the question
        // can be put to it.
        table.put("ObservationIncomplete", "asks the code/MAY_CHANGE");
        table.put("BorderValueUnreadable", "asks the reading/MAY_CHANGE");
        table.put("ModelReadingIncomplete", "asks the gap/UNAFFECTED");
        // And the seven where there is nothing further in to ask. Six of them are this compiler
        // meeting something it has no reading for; one is a figure of its own. A body the image
        // this run was made in does not carry is among them, and a wider run does not get past it —
        // what was elaborated is what the classes that ran came from.
        table.put("OutputCasesUnreadable", "answers/UNAFFECTED");
        table.put("InputCasesUnreadable", "answers/UNAFFECTED");
        table.put("BodyNotInEvaluation", "answers/UNAFFECTED");
        table.put("BoundaryNotDerived", "answers/UNAFFECTED");
        table.put("InputNotRead", "answers/UNAFFECTED");
        table.put("ProofContradicted", "answers/UNAFFECTED");
        table.put("ProofOfAWayContradicted", "answers/UNAFFECTED");
        table.put("ArmsUnsettled", "answers/UNAFFECTED");
        // The one arm that is a figure the query graph hands the analysis.
        table.put("PairSpaceTruncated", "answers/MAY_CHANGE");
        // And the figure the readings of one row are tried against: a build allowed more tries the
        // readings the walk stopped short of.
        table.put("BorderReadingsNotExhausted", "answers/MAY_CHANGE");
        // A coverage item's own place on the order is a question the exact arithmetic answers or
        // does not; a wider run does not change what scale a model's decimals were written at.
        table.put("ItemsPlaceNotWorkedOut", "answers/UNAFFECTED");
        // Which of the author's points a reading stands at is a question about how the reading
        // was derived, and a wider run derives it the same way.
        table.put("AReadingNotTiedToItsLine", "answers/UNAFFECTED");
        // Only what is first a fact of the weights: the exact arithmetic giving out, nothing read,
        // a border short with no word of its own, and a run nothing watched. What a border's own
        // reading stopped at stays that border's weakening, carried as it was said, so a row here
        // is the sample made with the arithmetic and the other ways are held in the figure test.
        table.put("AWeightNotDecided", "answers/UNAFFECTED");
        // A border nothing held against the lines beside it, which does not answer one way: a
        // strategy nobody wrote and rows all on one side are not allowances, and a run nobody
        // watched is. The row is written with the one that is, so what it shows is the answer
        // travelling rather than a constant.
        table.put("ABorderNotHeldAgainstTheLinesBesideIt", "asks what stood in the way/MAY_CHANGE");
        // And the same figure on the other criterion: a build allowed more walks the group.
        table.put("MeetingsNotWalked", "answers/MAY_CHANGE");
        // A meeting the classes do not place is placed the same way however much a run allows.
        table.put("MeetingsNotPlaced", "answers/UNAFFECTED");
        // And a sum whose decisions are not joined to evaluations is joined the same way.
        table.put("MeetingsNotJoined", "answers/UNAFFECTED");
        // A run this reading cannot place among the rules is not placed by allowing more.
        table.put("DecisionOfRowUnreadable", "answers/UNAFFECTED");
        // And a run nothing recorded is not recorded by allowing more either: what watched it is
        // what this build ran, and a wider run of the same build watches the same rows.
        table.put("DecisionRunNotWatched", "answers/UNAFFECTED");
        // A reading held to a larger figure gets further, so this one a wider run can answer.
        table.put("DecisionReadingIncomplete", "answers/MAY_CHANGE");
        // A rule read short is short of words, which no figure gives it.
        table.put("DecisionRuleReadShort", "answers/UNAFFECTED");
        // The rows written hold each key once, and a run allowed more writes no row that holds
        // one twice: what is short is a capacity and not a figure.
        table.put("KeyedOverwriteCasesUnmeasured", "answers/UNAFFECTED");
        // No row is written toward a node further down than the ones a row writes, and a run
        // allowed more of everything writes none either.
        table.put("ReachableNodeCasesUnmeasured", "answers/UNAFFECTED");
        // A rewrite left open asks why: a search stopped at how many rows a generation writes may
        // go further where more are allowed, and nothing else that leaves one open is an allowance.
        table.put("RewriteUndecided", "asks why it was left open/MAY_CHANGE");
        return table;
    }

    /** The table, held against what the arms answer, with the population read off the seal. */
    @Test
    void everyWeakeningSaysWhetherAWiderRunCouldAnswerIt() {
        Map<String, String> said = new LinkedHashMap<>();
        for (Weakening each : everyWeakening()) {
            said.put(each.getClass().getSimpleName(),
                    asks(each) + "/" + each.runSensitivity().name());
        }

        assertEquals(theWeakenings(), said);
    }

    /** Every member of the seal has a row, read from the seal rather than from the list. */
    @Test
    void everyWeakeningThereIsHasARowAbove() {
        Set<String> sealed = new LinkedHashSet<>();
        for (Class<?> each : Weakening.class.getPermittedSubclasses()) {
            sealed.add(each.getSimpleName());
        }
        Set<String> listed = new LinkedHashSet<>();
        for (Weakening each : everyWeakening()) {
            listed.add(each.getClass().getSimpleName());
        }

        assertEquals(sealed, listed, "a weakening no row above answers for");
    }

    /**
     * An arm that asks says what it was asked, and not something of its own.
     *
     * <p>What the rows above call {@code asks} is checked here rather than described. Each of the
     * three is made twice over the two answers the thing it holds can give, and has to come back
     * with each — an arm that quietly decided for itself would agree with one of them and not the
     * other.
     */
    @Test
    void anArmThatHoldsWhatStoppedItSaysWhatThatSays() {
        for (RunSensitivity each : RunSensitivity.values()) {
            Incompleteness.Cause cause = each == RunSensitivity.MAY_CHANGE
                    ? Incompleteness.Cause.at(Incompleteness.Code.VALUE_TRUNCATED,
                            Limits.DEFAULT.nodesFigure())
                    : Incompleteness.Cause.of(Incompleteness.Code.VALUE_UNREADABLE);

            assertEquals(each, Weakening.ObservationIncomplete.of(Incompleteness.atPosition(
                    cause, "b", "x")).runSensitivity());
            assertEquals(each, new Weakening.BorderValueUnreadable(
                    border(), ReadingGap.of(cause)).runSensitivity());
            assertEquals(each, new Weakening.ModelReadingIncomplete(
                    new ClosureGap.PositionNotReachedInto("b", new PositionId(TermPath.of("x")),
                            each == RunSensitivity.MAY_CHANGE
                                    ? new BlockReason.ValueRulesNotReachedPastDepthLimit()
                                    : new BlockReason.ValueRulesNotReached())).runSensitivity());
        }
    }

    /**
     * The one gap that answers for itself is right to, and this is what says so.
     *
     * <p>{@link ClosureGap.RulesNotReached} holds no reason: what a document says about a position
     * whose rules nothing enumerated is the hole, and which of the ways it was is kept inside
     * ({@link RulesLeftUnread}). So it answers {@code UNAFFECTED} from what can reach it, and a
     * third way of leaving rules unread that a wider run does get past would make that wrong with
     * nothing in the file to say so.
     *
     * <p>Asked of the type and not of a list: an arm added to {@code RulesLeftUnread} arrives here
     * whether or not anybody remembered this check.
     */
    @Test
    void nothingThatLeavesARulesUnreadIsSomethingAWiderRunGetsPast() {
        for (RulesLeftUnread each : everyWayRulesAreLeftUnread()) {
            assertEquals(RunSensitivity.UNAFFECTED, sensitivityOf(each),
                    () -> each + " reaches a `RulesNotReached`, which answers UNAFFECTED for all"
                            + " of them");
        }
    }

    /**
     * What a way of leaving rules unread says about a wider run.
     *
     * <p>Read off what it is rather than off a field, because {@link RulesLeftUnread} carries no
     * such answer and should not: it is a fact about how this compiler traverses a model, and the
     * one question asked of it here is whether any of its arms is a figure. None is — a clause this
     * reading lost, and a handing over nobody took over.
     */
    private static RunSensitivity sensitivityOf(RulesLeftUnread why) {
        return switch (why) {
            case RulesLeftUnread.ClauseOfThisReadingWasUnread _,
                 RulesLeftUnread.HandoffNotAccepted _ -> RunSensitivity.UNAFFECTED;
        };
    }

    /** One of each way rules are left unread, which is what a `RulesNotReached` is written from. */
    private static List<RulesLeftUnread> everyWayRulesAreLeftUnread() {
        return List.of(new RulesLeftUnread.ClauseOfThisReadingWasUnread(),
                new RulesLeftUnread.HandoffNotAccepted());
    }

    /** Whether the arm holds something to put the question to, which is what the rows record. */
    private static String asks(Weakening each) {
        return switch (each) {
            case Weakening.ObservationIncomplete _ -> "asks the code";
            case Weakening.BorderValueUnreadable _ -> "asks the reading";
            // What stood in the way, because the ways do not answer alike: a strategy nobody wrote
            // and rows all on one side are not allowances, and what a run watched is.
            case Weakening.ABorderNotHeldAgainstTheLinesBesideIt _ -> "asks what stood in the way";
            case Weakening.ModelReadingIncomplete _ -> "asks the gap";
            case Weakening.RewriteUndecided _ -> "asks why it was left open";
            case Weakening.OutputCasesUnreadable _, Weakening.InputCasesUnreadable _,
                 Weakening.BodyNotInEvaluation _, Weakening.BoundaryNotDerived _,
                 Weakening.InputNotRead _, Weakening.PairSpaceTruncated _,
                 Weakening.BorderReadingsNotExhausted _,
                 Weakening.ItemsPlaceNotWorkedOut _, Weakening.AReadingNotTiedToItsLine _,
                 Weakening.AWeightNotDecided _,
                 Weakening.ProofContradicted _, Weakening.ProofOfAWayContradicted _,
                 Weakening.ArmsUnsettled _,
                 Weakening.DecisionOfRowUnreadable _, Weakening.DecisionRunNotWatched _,
                 Weakening.MeetingsNotWalked _, Weakening.MeetingsNotPlaced _,
                 Weakening.MeetingsNotJoined _,
                 Weakening.DecisionReadingIncomplete _,
                 Weakening.DecisionRuleReadShort _,
                 Weakening.KeyedOverwriteCasesUnmeasured _,
                 Weakening.ReachableNodeCasesUnmeasured _ -> "answers";
        };
    }

    /**
     * One of each arm, made with whatever it takes.
     *
     * <p>The three that ask are made with a value that answers {@code MAY_CHANGE} where one can, so
     * the rows show the answer travelling rather than a constant. That each of them really does
     * travel both ways is {@link #anArmThatHoldsWhatStoppedItSaysWhatThatSays}'s.
     */
    private static List<Weakening> everyWeakening() {
        List<Weakening> out = new ArrayList<>();
        Incompleteness.Cause aLimit = Incompleteness.Cause.at(Incompleteness.Code.VALUE_TRUNCATED,
                Limits.DEFAULT.nodesFigure());
        out.add(Weakening.ObservationIncomplete.of(Incompleteness.atPosition(aLimit, "b", "x")));
        out.add(new Weakening.BorderValueUnreadable(border(), ReadingGap.of(aLimit)));
        out.add(new Weakening.ModelReadingIncomplete(new ClosureGap.RulesNotReached(
                "b", new PositionId(TermPath.of("x")))));
        RowRef unread = new RowRef("b", new SourceId("m.sou"), new RowIdentity.Unnamed(1));
        out.add(new Weakening.OutputCasesUnreadable("b", Set.of(unread)));
        out.add(new Weakening.InputCasesUnreadable("b", 0, Set.of(unread)));
        out.add(new Weakening.BodyNotInEvaluation("b"));
        out.add(new Weakening.BoundaryNotDerived("b"));
        out.add(new Weakening.InputNotRead("b"));
        out.add(new Weakening.ProofContradicted(new CoverageSites.Obligation("b",
                new SourceConstructOrigin(new WrittenOwner.Body("m", "b"), 2, 0,
                        SourceConstruct.IF),
                1, new DecidedBy.NotSaid())));
        out.add(new Weakening.ProofOfAWayContradicted("b", new DecisionRule(Map.of())));
        out.add(new Weakening.ArmsUnsettled(
                new SourceConstructOrigin(new WrittenOwner.Body("m", "b"), 1, 0,
                        SourceConstruct.IF)));
        out.add(new Weakening.PairSpaceTruncated("b", 9,
                WorkFigure.PAIRS_OF_CLASSES_COUNTED.at(4)));
        out.add(new Weakening.BorderReadingsNotExhausted(border(),
                WorkFigure.READINGS_OF_A_ROW_AT_A_POINT.at(4)));
        out.add(new Weakening.ItemsPlaceNotWorkedOut(border(),
                souther.compiler.numeric.UnheldNumber.MORE_ROOM_COULD_ANSWER));
        out.add(new Weakening.AReadingNotTiedToItsLine(border()));
        out.add(new Weakening.AWeightNotDecided("b", OneBorder.derivedValue(),
                new NumericTerm.ValueOf(TermPath.of("x")),
                Weakening.AWeightNotDecided.Why.THE_ARITHMETIC_GAVE_OUT));
        out.add(new Weakening.ABorderNotHeldAgainstTheLinesBesideIt(border(),
                Weakening.ABorderNotHeldAgainstTheLinesBesideIt.Why.NOTHING_WATCHED_THE_RUNS));
        out.add(new Weakening.MeetingsNotWalked("b", 1,
                List.of(WorkFigure.COMBINATIONS_OF_A_GROUP_MEASURED.at(4))));
        out.add(new Weakening.MeetingsNotPlaced("b", 1));
        out.add(new Weakening.MeetingsNotJoined("b", 1));
        out.add(new Weakening.DecisionOfRowUnreadable("b",
                souther.compiler.partition.RulesTaken.WhichRule.Why.NO_RECOGNISABLE_RULE_MATCHES));
        out.add(new Weakening.DecisionRunNotWatched("b"));
        out.add(new Weakening.DecisionReadingIncomplete("b",
                new souther.compiler.partition.DecisionReading.Enumeration.StoppedAtAFigure(
                        souther.compiler.partition.CompositionBudget
                                .PATHS_OF_A_DECISION_READ)));
        out.add(new Weakening.DecisionRuleReadShort("b"));
        out.add(new Weakening.KeyedOverwriteCasesUnmeasured("b"));
        out.add(new Weakening.ReachableNodeCasesUnmeasured("b"));
        out.add(new Weakening.RewriteUndecided("m", "b",
                new Replacement.ByOneAnswer(new ObservedValue.Integer(0),
                        new RowRef("b", new SourceId("m.sou"), new RowIdentity.Unnamed(1))),
                new ReplacementEvidence.Undecided(ReplacementEvidence.Undecided.Way.atFigures(
                        ReplacementEvidence.Undecided.Why.RUNS_SPENT,
                        List.of(WorkFigure.RUNS_REPLACING_AN_ARM.at(4)))).why()));
        return out;
    }

    /** One border, since which border it is is no part of what this is about. */
    private static Border border() {
        return OneBorder.border();
    }
}
