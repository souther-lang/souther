package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ArmReplacements;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.DecidedBy;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.PositionId;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.observe.Figure;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowRef;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.Border;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.ClosureGap;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.ReadingGap;
import souther.compiler.partition.Replacement;
import souther.compiler.partition.ReplacementDisposition;
import souther.compiler.partition.RulesTaken;
import souther.compiler.source.SourceId;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.ArrayList;
import java.util.EnumMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A weakening a wider run of this compiler may answer names the figure that stopped it, and one no
 * wider run answers names none.
 *
 * <p>The population is every arm, every value of what an arm asks, and every way a rewrite is left
 * open as the places that leave one open build it — so an arm or a reason added arrives here
 * without anybody remembering to add it.
 *
 * <p>Some are stopped where a wider run may get further and still name no figure, and each is
 * written down below with what it was stopped at instead. A list held both ways: a stop that comes
 * to name its figure has to be taken off it, and one that stops naming its figure has to be put on.
 */
class AWeakeningAWiderRunMayAnswerNamesTheFigureThatStoppedItTest {

    /**
     * What a wider run may answer and nothing here names a figure for, and why.
     *
     * <p>A border nothing watched the runs for was stopped by how this build was asked to run, which
     * is no figure. It is the one.
     */
    private static Set<String> wideningWithoutAFigure() {
        return Set.of("ABorderNotHeldAgainstTheLinesBesideIt NOTHING_WATCHED_THE_RUNS");
    }

    @Test
    void aWeakeningNoWiderRunAnswersNamesNoFigure() {
        for (Map.Entry<String, Weakening> each : everyWeakening().entrySet()) {
            if (each.getValue().runSensitivity() == RunSensitivity.UNAFFECTED) {
                assertEquals(List.of(), each.getValue().figures(), each.getKey());
            }
        }
    }

    @Test
    void aWeakeningAWiderRunMayAnswerNamesAFigureOrIsSaidNotTo() {
        Set<String> without = new LinkedHashSet<>();
        for (Map.Entry<String, Weakening> each : everyWeakening().entrySet()) {
            if (each.getValue().runSensitivity() == RunSensitivity.MAY_CHANGE
                    && each.getValue().figures().isEmpty()) {
                without.add(each.getKey());
            }
        }

        assertEquals(wideningWithoutAFigure(), without);
    }

    /**
     * An arm that holds what stopped it hands over exactly what that names, as it hands over what
     * that says about a wider run: whether those name a figure is theirs to answer.
     */
    @Test
    void anArmThatHoldsWhatStoppedItNamesWhatThatNames() {
        for (Incompleteness.Code code : Incompleteness.Code.values()) {
            ReadingGap gap = ReadingGap.of(causeOf(code));
            assertEquals(gap.figures(),
                    new Weakening.BorderValueUnreadable(border(), gap).figures(), code::name);
        }
        for (ClosureGap gap : closureGaps()) {
            assertEquals(gap.figures(), new Weakening.ModelReadingIncomplete(gap).figures(),
                    gap::toString);
        }
    }

    /**
     * Two lines of one border whose values one code stopped at two figures are one fact, met at
     * both: what told them apart is what evidenced the fact, and a reader is told the fact once.
     */
    @Test
    void oneCodeAtOneBorderIsOneFactAtEveryFigureItWasMetAt() {
        Figure depth = WorkFigure.OBSERVED_DEPTH.at(12);
        Figure text = WorkFigure.OBSERVED_TEXT.at(1024);
        Weakening atTheDepth = new Weakening.BorderValueUnreadable(border(), ReadingGap.of(
                Incompleteness.Cause.at(Incompleteness.Code.VALUE_TRUNCATED, depth)));
        Weakening atTheText = new Weakening.BorderValueUnreadable(border(), ReadingGap.of(
                Incompleteness.Cause.at(Incompleteness.Code.VALUE_TRUNCATED, text)));

        WeakeningSet both = WeakeningSet.of(atTheDepth).union(WeakeningSet.of(atTheText));

        assertEquals(1, both.causes().size(), both::toString);
        assertEquals(Set.copyOf(List.of(depth, text)),
                Set.copyOf(both.causes().iterator().next().figures()), both::toString);
    }

    /**
     * One rewrite left open for one reason is one fact at every figure it was met at, and one
     * weakening that names them all.
     *
     * <p>What tells two of these apart is which rewrite and the reasons it was left open for. A
     * search held to one number of runs by one measure and to another by the next left one rewrite
     * open for one reason, and a reader counting the verdict's openings counts it once.
     */
    @Test
    void oneRewriteLeftOpenAtTwoFiguresIsOneFactAtBoth() {
        Figure four = WorkFigure.RUNS_REPLACING_AN_ARM.at(4);
        Figure eight = WorkFigure.RUNS_REPLACING_AN_ARM.at(8);
        Replacement rewrite = new Replacement.ByOneAnswer(new ObservedValue.Integer(0),
                new RowRef("b", new SourceId("m.sou"), new RowIdentity.Unnamed(1)));

        WeakeningSet both = WeakeningSet.of(
                new Weakening.RewriteUndecided("b", rewrite, runsSpentAt(four)),
                new Weakening.RewriteUndecided("b", rewrite, runsSpentAt(eight)));

        assertEquals(Set.of(new Weakening.RewriteUndecided("b", rewrite,
                        new ReplacementEvidence.Undecided(ReplacementEvidence.Undecided.Way
                                .atFigures(ReplacementEvidence.Undecided.Why.RUNS_SPENT,
                                        List.of(four, eight))).why())),
                both.causes());
    }

    /** And so is every other arm that carries the figures it stopped at beside what it is. */
    @Test
    void anArmStoppedAtTwoFiguresIsOneFactAtBoth() {
        Figure one = WorkFigure.READINGS_OF_A_ROW_AT_A_POINT.at(64);
        Figure other = WorkFigure.READINGS_OF_A_ROW_AT_A_POINT.at(128);

        assertEquals(Set.of(new Weakening.BorderReadingsNotExhausted(border(),
                        List.of(one, other))),
                WeakeningSet.of(new Weakening.BorderReadingsNotExhausted(border(), one),
                        new Weakening.BorderReadingsNotExhausted(border(), other)).causes());
        assertEquals(Set.of(new Weakening.PairSpaceTruncated("b", 9, List.of(one, other))),
                WeakeningSet.of(new Weakening.PairSpaceTruncated("b", 9, one),
                        new Weakening.PairSpaceTruncated("b", 9, other)).causes());
        assertEquals(Set.of(new Weakening.MeetingsNotWalked("b", 2, List.of(one, other))),
                WeakeningSet.of(new Weakening.MeetingsNotWalked("b", 2, List.of(other)),
                        new Weakening.MeetingsNotWalked("b", 2, List.of(one))).causes());
    }

    private static ReplacementEvidence.Undecided.LeftOpen runsSpentAt(Figure runs) {
        return new ReplacementEvidence.Undecided(ReplacementEvidence.Undecided.Way.atFigures(
                ReplacementEvidence.Undecided.Why.RUNS_SPENT, List.of(runs))).why();
    }

    /** Every member of the seal is among them, read from the seal rather than from the list. */
    @Test
    void everyArmIsAmongThem() {
        Set<String> sealed = new LinkedHashSet<>();
        for (Class<?> each : Weakening.class.getPermittedSubclasses()) {
            sealed.add(each.getSimpleName());
        }
        Set<String> swept = new LinkedHashSet<>();
        everyWeakening().values().forEach(each -> swept.add(each.getClass().getSimpleName()));

        assertEquals(sealed, swept);
    }

    /** Every reason a rewrite is left open is among the ways swept. */
    @Test
    void everyReasonARewriteIsLeftOpenIsAmongThem() {
        Set<ReplacementEvidence.Undecided.Why> swept = new LinkedHashSet<>();
        everyWayARewriteIsLeftOpen().forEach(each -> swept.add(each.why()));

        assertEquals(Set.of(ReplacementEvidence.Undecided.Why.values()), swept);
    }

    /**
     * Every arm with what it holds, by a label saying which; the ones that hold what stopped them
     * once for each stop they can hold.
     */
    private static Map<String, Weakening> everyWeakening() {
        Map<String, Weakening> out = new LinkedHashMap<>();
        for (Incompleteness.Code code : Incompleteness.Code.values()) {
            out.put("ObservationIncomplete " + code, Weakening.ObservationIncomplete.of(
                    Incompleteness.atPosition(causeOf(code), "b", "x")));
            out.put("BorderValueUnreadable " + code,
                    new Weakening.BorderValueUnreadable(border(), ReadingGap.of(causeOf(code))));
        }
        for (ClosureGap gap : closureGaps()) {
            out.put("ModelReadingIncomplete " + gap, new Weakening.ModelReadingIncomplete(gap));
        }
        out.put("OutputCasesUnreadable", new Weakening.OutputCasesUnreadable("b"));
        out.put("InputCasesUnreadable", new Weakening.InputCasesUnreadable("b", 0));
        out.put("ItemsPlaceNotWorkedOut", new Weakening.ItemsPlaceNotWorkedOut(border(),
                UnheldNumber.MORE_ROOM_COULD_ANSWER));
        out.put("AReadingNotTiedToItsLine", new Weakening.AReadingNotTiedToItsLine(border()));
        out.put("BorderReadingsNotExhausted", new Weakening.BorderReadingsNotExhausted(border(),
                WorkFigure.READINGS_OF_A_ROW_AT_A_POINT.at(256)));
        for (Weakening.ABorderNotHeldAgainstTheLinesBesideIt.Why why
                : Weakening.ABorderNotHeldAgainstTheLinesBesideIt.Why.values()) {
            out.put("ABorderNotHeldAgainstTheLinesBesideIt " + why,
                    new Weakening.ABorderNotHeldAgainstTheLinesBesideIt(border(), why));
        }
        out.put("BodyNotInEvaluation", new Weakening.BodyNotInEvaluation("b"));
        out.put("BoundaryNotDerived", new Weakening.BoundaryNotDerived("b"));
        out.put("InputNotRead", new Weakening.InputNotRead("b"));
        out.put("PairSpaceTruncated", new Weakening.PairSpaceTruncated("b", 9,
                WorkFigure.PAIRS_OF_CLASSES_COUNTED.at(4)));
        out.put("ProofContradicted", new Weakening.ProofContradicted(new CoverageSites.Obligation(
                "b", new SourceConstructOrigin(new WrittenOwner.Body("m", "b"), 2, 0,
                        SourceConstruct.IF),
                1, new DecidedBy.NotSaid())));
        out.put("ProofOfAWayContradicted",
                new Weakening.ProofOfAWayContradicted("b", new DecisionRule(Map.of())));
        out.put("ArmsUnsettled", new Weakening.ArmsUnsettled(new SourceConstructOrigin(
                new WrittenOwner.Body("m", "b"), 1, 0, SourceConstruct.IF)));
        for (RulesTaken.WhichRule.Why why : RulesTaken.WhichRule.Why.values()) {
            out.put("DecisionOfRowUnreadable " + why,
                    new Weakening.DecisionOfRowUnreadable("b", why));
        }
        out.put("DecisionRunNotWatched", new Weakening.DecisionRunNotWatched("b"));
        out.put("MeetingsNotWalked", new Weakening.MeetingsNotWalked("b", 1,
                List.of(WorkFigure.COMBINATIONS_OF_A_GROUP_MEASURED.at(4))));
        out.put("MeetingsNotPlaced", new Weakening.MeetingsNotPlaced("b", 1));
        out.put("MeetingsNotJoined", new Weakening.MeetingsNotJoined("b", 1));
        out.put("DecisionReadingIncomplete", new Weakening.DecisionReadingIncomplete("b",
                new DecisionReading.Enumeration.StoppedAtAFigure(
                        CompositionBudget.PATHS_OF_A_DECISION_READ)));
        out.put("DecisionRuleReadShort", new Weakening.DecisionRuleReadShort("b"));
        out.put("KeyedOverwriteCasesUnmeasured", new Weakening.KeyedOverwriteCasesUnmeasured("b"));
        out.put("ReachableNodeCasesUnmeasured", new Weakening.ReachableNodeCasesUnmeasured("b"));
        Replacement rewrite = new Replacement.ByOneAnswer(new ObservedValue.Integer(0),
                new RowRef("b", new SourceId("m.sou"), new RowIdentity.Unnamed(1)));
        for (ReplacementEvidence.Undecided.Way way : everyWayARewriteIsLeftOpen()) {
            Weakening.RewriteUndecided undecided = new Weakening.RewriteUndecided("b", rewrite,
                    new ReplacementEvidence.Undecided(way).why());
            out.putIfAbsent("RewriteUndecided " + way.why()
                    + (way.figures().isEmpty() ? "" : " " + way.figures()), undecided);
        }
        return out;
    }

    /**
     * Every way a rewrite is left open, as the places that leave one open build it: what a search
     * that found nothing ended in, handed what the search carries for each; what a sibling the
     * classes do not carry leaves; and what the rows leave where they cannot be asked.
     */
    private static List<ReplacementEvidence.Undecided.Way> everyWayARewriteIsLeftOpen() {
        List<ReplacementEvidence.Undecided.Way> out = new ArrayList<>();
        for (ReplacementDisposition.Ended ended : ReplacementDisposition.Ended.values()) {
            if (ended == ReplacementDisposition.Ended.ROWS_A_BLOCK_MAY_HOLD) {
                continue;   // only ever of a search for a block, which the measure never asks
            }
            for (ReplacementDisposition.Met carried : carriedFor(ended)) {
                Map<ReplacementDisposition.Ended, ReplacementDisposition.Met> one =
                        new EnumMap<>(ReplacementDisposition.Ended.class);
                one.put(ended, carried);
                out.addAll(Replacements.Measured.whyNoneFound(one));
            }
        }
        out.add(ReplacementReading.wayOf(new ArmReplacements.Sibling.Why.PastWhatAForkCarries(
                WorkFigure.NODES_A_FORK_CARRIES.at(4000))));
        out.add(ReplacementReading.wayOf(new ArmReplacements.Sibling.Why.PastWhatAMethodHolds()));
        out.add(ReplacementEvidence.Undecided.Way.atNoAllowance(
                ReplacementEvidence.Undecided.Why.A_STATEMENT_WAS_NOT_READ));
        return out;
    }

    /**
     * What the search carries out of each way it ends: the runs it was allowed where it ran out of
     * them; the composing's figure, or a bound of the search's own, where composing stopped; the
     * limit a run went past where one did, something no run allows where every run that did not
     * come back stopped at that, and both where some did each; and nothing elsewhere.
     */
    private static List<ReplacementDisposition.Met> carriedFor(
            ReplacementDisposition.Ended ended) {
        return switch (ended) {
            case RUNS_A_REWRITE_MAY_TAKE -> List.of(ReplacementDisposition.Met.at(
                    List.of(WorkFigure.RUNS_REPLACING_AN_ARM.at(4))));
            case A_FIGURE_OF_THE_COMPOSING -> List.of(
                    ReplacementDisposition.Met.at(
                            List.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.figure())),
                    ReplacementDisposition.Met.at(
                            List.of(WorkFigure.CANDIDATES_A_REPAIR_BUILDS.at(64))));
            case A_RUN_DID_NOT_COME_BACK -> List.of(
                    ReplacementDisposition.Met.at(List.of(WorkFigure.EVALUATION_STEPS.at(100))),
                    ReplacementDisposition.Met.AT_NO_FIGURE,
                    // One run stopped at a figure and at the host's stack, and one run at each.
                    ReplacementDisposition.Met.once(
                            List.of(WorkFigure.EVALUATION_STEPS.at(100)), true),
                    ReplacementDisposition.Met.at(List.of(WorkFigure.EVALUATION_STEPS.at(100)))
                            .and(ReplacementDisposition.Met.AT_NO_FIGURE));
            case EVERY_ROW_ANSWERED_ALIKE, NOTHING_WAS_COMPOSED, ROWS_A_BLOCK_MAY_HOLD,
                 NOTHING_RAN -> List.of(ReplacementDisposition.Met.AT_NO_FIGURE);
        };
    }

    /** What happened under {@code code}, at a figure exactly where the code says one decides. */
    private static Incompleteness.Cause causeOf(Incompleteness.Code code) {
        return code.runSensitivity() == RunSensitivity.MAY_CHANGE
                ? Incompleteness.Cause.at(code, WorkFigure.EVALUATION_STEPS.at(100))
                : Incompleteness.Cause.of(code);
    }

    /** One of each way a reading of the model is left open. */
    private static List<ClosureGap> closureGaps() {
        PositionId at = new PositionId(TermPath.of("x"));
        return List.of(
                new ClosureGap.RulesNotReached("b", at),
                new ClosureGap.PositionNotReachedInto("b", at,
                        new BlockReason.ValueRulesNotReachedPastDepthLimit()),
                new ClosureGap.PositionNotReachedInto("b", at,
                        new BlockReason.ValueRulesNotReached()));
    }

    /** One border, since which border it is is no part of what this is about. */
    private static Border border() {
        return OneBorder.border();
    }
}
