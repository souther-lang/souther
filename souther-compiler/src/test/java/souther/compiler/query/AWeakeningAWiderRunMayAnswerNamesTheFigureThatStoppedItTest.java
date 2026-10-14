package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BehaviorContract;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.RuleRef;
import souther.compiler.coverage.ArmReplacements;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.DecidedBy;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PositionId;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.observe.Figure;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowRef;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.Border;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.ClauseStatementId;
import souther.compiler.partition.ClosureGap;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.Level;
import souther.compiler.partition.LineFacts;
import souther.compiler.partition.LineOrigin;
import souther.compiler.partition.ReadingGap;
import souther.compiler.partition.Replacement;
import souther.compiler.partition.ReplacementDisposition;
import souther.compiler.partition.RulesTaken;
import souther.compiler.partition.WhichLine;
import souther.compiler.check.PartId;
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
        out.put("ArmsUnsettled", new Weakening.ArmsUnsettled(new SourceConstructOrigin(
                new WrittenOwner.Body("m", "b"), 1, 0, SourceConstruct.IF)));
        for (RulesTaken.WhichRule.Why why : RulesTaken.WhichRule.Why.values()) {
            out.put("DecisionOfRowUnreadable " + why,
                    new Weakening.DecisionOfRowUnreadable("b", why));
        }
        out.put("DecisionRunNotWatched", new Weakening.DecisionRunNotWatched("b"));
        out.put("MeetingsNotWalked", new Weakening.MeetingsNotWalked("b", 1,
                List.of(WorkFigure.COMBINATIONS_OF_A_GROUP_MEASURED.at(4))));
        out.put("DecisionReadingIncomplete", new Weakening.DecisionReadingIncomplete("b",
                new DecisionReading.Enumeration.StoppedAtAFigure(
                        CompositionBudget.PATHS_OF_A_DECISION_READ)));
        out.put("DecisionRuleReadShort", new Weakening.DecisionRuleReadShort("b"));
        out.put("KeyedOverwriteCasesUnmeasured", new Weakening.KeyedOverwriteCasesUnmeasured("b"));
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
            for (List<Figure> carried : carriedFor(ended)) {
                Map<ReplacementDisposition.Ended, List<Figure>> one =
                        new EnumMap<>(ReplacementDisposition.Ended.class);
                one.put(ended, carried);
                out.addAll(Replacements.Measured.whyNoneFound(one));
            }
        }
        out.add(ReplacementReading.wayOf(new ArmReplacements.Sibling.Why.PastWhatAForkCarries(
                WorkFigure.NODES_A_FORK_CARRIES.at(4000))));
        out.add(ReplacementReading.wayOf(new ArmReplacements.Sibling.Why.PastWhatAMethodHolds()));
        out.add(new ReplacementEvidence.Undecided.Way.AtNoAllowance(
                ReplacementEvidence.Undecided.Why.A_STATEMENT_WAS_NOT_READ));
        return out;
    }

    /**
     * What the search carries out of each way it ends: the runs it was allowed where it ran out of
     * them; the composing's figure, or a bound of the search's own, where composing stopped; the
     * limit a run went past where one did, and none where every run that did not come back stopped
     * at something no run allows; and nothing elsewhere.
     */
    private static List<List<Figure>> carriedFor(ReplacementDisposition.Ended ended) {
        return switch (ended) {
            case RUNS_A_REWRITE_MAY_TAKE -> List.of(
                    List.of(WorkFigure.RUNS_REPLACING_AN_ARM.at(4)));
            case A_FIGURE_OF_THE_COMPOSING -> List.of(
                    List.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.figure()),
                    List.of(WorkFigure.CANDIDATES_A_REPAIR_BUILDS.at(64)));
            case A_RUN_DID_NOT_COME_BACK -> List.of(
                    List.of(WorkFigure.EVALUATION_STEPS.at(100)), List.of());
            case EVERY_ROW_ANSWERED_ALIKE, NOTHING_WAS_COMPOSED, ROWS_A_BLOCK_MAY_HOLD,
                 NOTHING_RAN -> List.of(List.of());
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
        Carrier carrier = new Carrier.Whole();
        NumericTerm.ValueOf value = new NumericTerm.ValueOf(TermPath.of("x"));
        BoundaryTarget target = BoundaryTarget.at(
                new BorderQuantity.OfACoordinate("cap", value,
                        TermOrdersFixtures.itself(value, carrier)),
                new Level.OnACarrier(carrier, Count.of(100)));
        LineOrigin origin = new LineOrigin.EnsuresOrigin(
                new WhichLine.OfAComparisonOfAPart(new ClauseStatementId(new PartId<>(
                        new RuleRef.Ensures(new BehaviorContract.RuleId(null, 0, 0, null), "cap"),
                        0), 0)),
                new LineFacts(new ComparisonClaim.Cut(Towards.BELOW, true)));
        return Border.at(target, origin, new NumericDomain.Bounds(null, null));
    }
}
