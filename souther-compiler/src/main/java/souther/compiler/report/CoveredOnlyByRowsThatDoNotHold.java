package souther.compiler.report;

import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.ArmCoverage;
import souther.compiler.query.ArmObligation;
import souther.compiler.query.ArmSummary;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.CombinationCriterion;
import souther.compiler.query.DecisionEvidence;
import souther.compiler.query.InteractionEvidence;
import souther.compiler.query.ObligationCoverage;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.query.RowWitnesses;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * The obligations of one behavior some row covers and only rows that do not hold do, measure by
 * measure.
 *
 * <p>Every one of them is met, and counted as met: whatever a row that does not hold reached before
 * it stopped, it reached. What these are is the part of the count that rests on those rows alone —
 * taken away, the obligation is not covered — which nothing in the count says. Read off the
 * witnesses the measures kept and off nothing else. How many a page marked is counted where the
 * page writes the marks and not here: a section can have reasons of its own not to be written.
 *
 * <p>Only what a report shows a count of. The combinations of two classes are counted under the
 * fallback and the combinations of decisions under the interactions, never both, so only the one the
 * behavior is held to is here.
 */
public record CoveredOnlyByRowsThatDoNotHold(
        List<Covered<PartitionEvidence.AxisClass>> classes,
        List<Covered<PartitionEvidence.PairSpace.Cell>> combinationsOfClasses,
        List<Covered<BorderObligationPointAssessment>> points,
        List<Covered<ArmObligation.Counted>> arms,
        List<Covered<DecisionReading.Stated>> rules,
        List<Covered<ObligationIdentity.OfACombinationOfDecisions>> combinationsOfDecisions) {

    public CoveredOnlyByRowsThatDoNotHold {
        classes = List.copyOf(classes);
        combinationsOfClasses = List.copyOf(combinationsOfClasses);
        points = List.copyOf(points);
        arms = List.copyOf(arms);
        rules = List.copyOf(rules);
        combinationsOfDecisions = List.copyOf(combinationsOfDecisions);
    }

    /**
     * One obligation and the rows that cover it.
     *
     * @param obligation what is covered
     * @param by         the rows, every one of which does not hold
     */
    public record Covered<T>(T obligation, RowWitnesses.OnlyRowsThatDoNotHold by) {}

    /** What {@code behavior}'s measures kept. */
    static CoveredOnlyByRowsThatDoNotHold of(AdequacyReport.BehaviorReport behavior) {
        List<Covered<PartitionEvidence.AxisClass>> classes = new ArrayList<>();
        List<Covered<PartitionEvidence.PairSpace.Cell>> cells = new ArrayList<>();
        PartitionEvidence partition = behavior.partition();
        if (partition != null) {
            for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
                axis.reached().made().ifPresent(reached -> reached.witnessed().forEach(
                        (id, by) -> only(by, new PartitionEvidence.AxisClass(axis, id), classes)));
            }
        }
        if (behavior.evidence().combinations() instanceof CombinationCriterion.PairFallback(
                PartitionEvidence.PairSpace space)) {
            space.counted().made().ifPresent(made -> made.byPair().values().forEach(
                    reached -> reached.forEach((cell, by) -> only(by, cell, cells))));
        }
        List<Covered<BorderObligationPointAssessment>> points = new ArrayList<>();
        for (BorderObligationPointAssessment point : behavior.account()) {
            if (point.owed().coverage() instanceof ObligationCoverage.Witnessed(RowWitnesses by)) {
                only(by, point, points);
            }
        }
        List<Covered<ArmObligation.Counted>> arms = new ArrayList<>();
        Adequacy.BranchEvidence branch = behavior.branch();
        if (branch != null) {
            for (ArmObligation.Counted arm : branch.measured().made()
                    .map(ArmSummary::met).orElseGet(List::of)) {
                if (arm.coverage().made().orElse(null) instanceof ArmCoverage.Hit(RowWitnesses by)) {
                    only(by, arm, arms);
                }
            }
        }
        List<Covered<DecisionReading.Stated>> rules = rulesOf(behavior.evidence().decision());
        List<Covered<ObligationIdentity.OfACombinationOfDecisions>> meetings = new ArrayList<>();
        if (behavior.evidence().combinations() instanceof CombinationCriterion.Interactions(
                InteractionEvidence measured)) {
            measured.made().made().map(InteractionEvidence.RowsMeeting::made).orElseGet(Map::of)
                    .forEach((combination, by) -> only(by, combination, meetings));
        }
        return new CoveredOnlyByRowsThatDoNotHold(classes, cells, points, arms, rules, meetings);
    }

    /**
     * What a module's declarations are owed that only rows that do not hold stand at.
     *
     * <p>Beside the behaviors' and never in any one of them: a line a declaration drew is owed once
     * for the module and met by a row of whichever behavior carries the type.
     */
    static List<Covered<Adequacy.DeclaredDebt>> debtsOf(List<Adequacy.DeclaredDebt> debts) {
        List<Covered<Adequacy.DeclaredDebt>> out = new ArrayList<>();
        for (Adequacy.DeclaredDebt each : debts) {
            if (each.debt().owed().coverage() instanceof ObligationCoverage.Witnessed(
                    RowWitnesses by)) {
                only(by, each, out);
            }
        }
        return out;
    }

    /**
     * The rules of {@code decision} only rows that do not hold take.
     *
     * <p>Asked on its own as well, by the assembly of a report: a rule a page names is one it is
     * handed the conditions of, and which rules those are has to be known before there is a
     * behavior's report to ask.
     */
    static List<Covered<DecisionReading.Stated>> rulesOf(DecisionEvidence decision) {
        List<Covered<DecisionReading.Stated>> rules = new ArrayList<>();
        if (decision != null) {
            decision.took().made().ifPresent(placed -> {
                for (DecisionReading.Stated stated : decision.read().stated()) {
                    RowWitnesses by = placed.taken().get(stated.rule());
                    if (by != null) {
                        only(by, stated, rules);
                    }
                }
            });
        }
        return rules;
    }

    private static <T> void only(RowWitnesses by, T obligation, List<Covered<T>> into) {
        if (by instanceof RowWitnesses.OnlyRowsThatDoNotHold only) {
            into.add(new Covered<>(obligation, only));
        }
    }
}
