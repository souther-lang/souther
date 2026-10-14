package souther.compiler.query;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.partition.DecisionCondition;
import souther.compiler.partition.ShownBy;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * One condition of a decision rule, as a reader is told about it.
 *
 * <p><b>{@code DecisionRule} is for identity; this is for explanation.</b> A rule is told apart by
 * the distinctions it consulted, written the one way round that makes a comparison and its denial
 * one column — so {@code n > 100} in the source is held as the proposition {@code n <= 100} denied.
 * That is what an account has to key on and it is not what an author wrote. Rendered into a
 * sentence, it would show somebody a comparison they did not write, the wrong way round, and the
 * canonicalisation this compiler does for its own sake would arrive as a claim about their model.
 *
 * <p>So a reader is sent to the construct instead. {@link ShownBy} names which construct of the
 * model each condition is and what a run down the path would be seen doing there; a sentence says
 * which construct and which way it went, and the author reads their own comparison at the place it
 * points to.
 *
 * <p>Made once for both surfaces. A report and a warning say this differently — a report can name a
 * file and a diagnostic cannot — and what they may not do is read the rule apart twice, which is
 * how one of them would come to word a condition the other does not have.
 *
 * <p><b>Nothing is dropped.</b> A rule's conditions are what tell it from the rules beside it, and
 * two findings whose sentences say only which behavior they are of are two findings a reader cannot
 * act on. A condition with no construct to point at is said as that rather than left out, and never
 * stood in for by the proposition the account keys on.
 */
public sealed interface DecisionRuleReading {

    /**
     * A comparison the author wrote, coming out one way.
     *
     * <p>The site and not the occurrence. Where a comparison is written is a thing the coverage
     * sites already hold, and a reader sent there by a second answer would be sent by whichever of
     * the two had been kept in step.
     *
     * @param comparison which comparison of the model, which is what a reader is sent to
     * @param held       whether the path took it holding — of the comparison as written, not of the
     *                   proposition the rule is keyed on
     * @param within     which copy of it, as {@link AForkTookAnArm#within} says
     */
    record AComparisonCameOut(CoverageSites.ComparisonSite comparison, boolean held,
                              ExpansionLineage within) implements DecisionRuleReading {

        public AComparisonCameOut {
            Objects.requireNonNull(comparison, "a comparison of the model is some site");
            Objects.requireNonNull(within, "a comparison is where it is written or in some copy");
        }
    }

    /**
     * An application of one of the language's operations the author wrote, answering one way.
     *
     * @param application where the code answering it stands, which is what a reader is sent to
     * @param held        whether the path took it answering true
     * @param within      which copy of it, as {@link AForkTookAnArm#within} says
     */
    record AnApplicationAnswered(CoverageSites.AnswerSite application, boolean held,
                                 ExpansionLineage within) implements DecisionRuleReading {

        public AnApplicationAnswered {
            Objects.requireNonNull(application, "an application of the model is some site");
            Objects.requireNonNull(within, "an application is where it is written or in some copy");
        }
    }

    /**
     * A construct of the model answering a truth — a comparison or an application — that this run
     * has no site for.
     *
     * <p>Beside {@link AConditionIsNotShown} for the reason {@link AForkIsNotPlaced} is: this is
     * the plan that numbered the places having nothing under the construct the reading named,
     * rather than the reading of the body falling short of saying what a condition means.
     */
    record AnOutcomeIsNotPlaced(ModelOccurrence construct, boolean held)
            implements DecisionRuleReading {

        public AnOutcomeIsNotPlaced {
            Objects.requireNonNull(construct, "a truth of the model is some construct's");
        }
    }

    /**
     * A fork of the model, with the path going down one of its arms.
     *
     * <p>The site and not the fork and a number. Which arm a reader is told about is a thing the
     * coverage sites already have words for, and a sentence built from the number would be a second
     * naming of one arm, free to call it something the branch account does not.
     *
     * @param arm    which arm of the model, which is what a reader is sent to
     * @param within which copy of the fork: the calls of the model's own values the path went
     *               through to reach it, and {@link ExpansionLineage#ORIGINAL} where it stands in
     *               the body itself. The site is one per construct, and a value called twice is one
     *               construct standing in two places — a path through both copies, one each way,
     *               said by the sites alone reads the same as the path the other way round
     */
    record AForkTookAnArm(CoverageSites.ArmSite arm, ExpansionLineage within)
            implements DecisionRuleReading {

        public AForkTookAnArm {
            Objects.requireNonNull(arm, "an arm of the model is some site");
            Objects.requireNonNull(within, "a fork is where it is written or in some copy");
        }
    }

    /**
     * A condition of the rule this reading had no words for.
     *
     * <p>There is nothing to point at, and what a reader is owed is that the rule turns on
     * something this compiler cannot show them.
     *
     * <p>The condition is carried for whoever is debugging this compiler and is not what a sentence
     * says. Written into one, the proposition an account keys on would be shown to an author as
     * their own comparison — which is the one thing this whole reading is arranged against.
     */
    record AConditionIsNotShown(DecisionCondition condition) implements DecisionRuleReading {

        public AConditionIsNotShown {
            Objects.requireNonNull(condition, "a condition nothing shows is some condition");
        }
    }

    /**
     * A fork of the model this run has no site for.
     *
     * <p>Beside {@link AConditionIsNotShown} and not among it. That one is the reading of the body
     * falling short of saying what a condition means; this is the plan that numbered the places
     * having nothing under the construct the reading named — a different thing to chase, and a
     * reader told the first would go looking for a shape this compiler cannot read.
     */
    record AForkIsNotPlaced(ModelOccurrence fork, int part) implements DecisionRuleReading {

        public AForkIsNotPlaced {
            Objects.requireNonNull(fork, "an arm is an arm of some fork of the model");
        }
    }

    /**
     * Every condition of {@code ruled}, in the order the author wrote them.
     *
     * <p>One reading per condition and never fewer. The arms are resolved against the plan that
     * numbered the sites, which is where a fork of the model and a place a run is recorded at are
     * already related; a fork the plan has no site for is said as a condition nothing shows rather
     * than left out, so the count of what a reader is told matches the rule.
     */
    static List<DecisionRuleReading> of(souther.compiler.partition.DecisionReading.Ruled ruled,
                                        CoverageSites.Plan plan, String behavior) {
        List<DecisionRuleReading> out = new ArrayList<>();
        for (ShownBy each : ruled.shownBy()) {
            out.add(switch (each) {
                case ShownBy.AtAnOutcome(var construct, var held) ->
                        outcomeOf(plan, behavior, construct, held);
                case ShownBy.AtAnArm(var fork, var part) -> armOf(plan, behavior, fork, part);
                // The arm is the place a reader is sent to: the operand not run is what the run
                // there did not do, and there is no place to send anyone for that.
                case ShownBy.AtAnArmShortOf(var fork, var part, var _) ->
                        armOf(plan, behavior, fork, part);
                case ShownBy.ShortOf(var condition, var _) -> new AConditionIsNotShown(condition);
                case ShownBy.NothingIsRecorded(var condition) ->
                        new AConditionIsNotShown(condition);
            });
        }
        return List.copyOf(out);
    }

    /**
     * What a run that came one way to a combination of a body's decisions would be seen doing, one
     * reading per place, in the order the way holds them.
     *
     * <p>Read off the places and not off the decisions the combination is told apart by. Those are
     * held in the terms a search steers a row by, and a sentence made of them would name input
     * positions the way this compiler spells them; the places are the comparisons, applications and
     * arms the author wrote, and each is resolved by the rule a decision rule's conditions are, on
     * the construct of the model the place is a materialisation of.
     *
     * <p>A copy of a construct said once. One arm can stand for several conditions — a run down it
     * brought every truth of the condition out the way the arm says — and a sentence for each would
     * be the same sentence.
     */
    static List<DecisionRuleReading> ofAWay(List<ControlClaim> claims, CoverageSites.Plan plan,
                                            String behavior) {
        Set<DecisionRuleReading> out = new LinkedHashSet<>();
        for (ControlClaim claim : claims) {
            out.add(switch (claim.at()) {
                case ControlPlace.Outcome(var occurrence, var _, var held) ->
                        outcomeOf(plan, behavior, copyOf(occurrence), held);
                case ControlPlace.Arm(var arm, var _, var _) ->
                        armOf(plan, behavior, copyOf(arm.fork()), arm.part());
            });
        }
        return List.copyOf(out);
    }

    /**
     * The construct {@code occurrence} is, in the copy of the model it stands in.
     *
     * <p>A construct inside one of the language's own operations is no construct of the model, and
     * a place there is still a place a run is recorded at — {@code Int.max} draws a line of its own
     * and its arms are owed. It is found by its origin as any construct is, and the copy it stands
     * in is the copy the call of the operation stands in, which is what tells two such calls apart.
     */
    private static ModelOccurrence copyOf(ConstructOccurrence occurrence) {
        return ModelOccurrence.statedAt(occurrence)
                .orElseGet(() -> new ModelOccurrence(occurrence.origin(),
                        ModelOccurrence.operationCalledAround(occurrence)
                                .map(ModelOccurrence::lineage)
                                .orElse(ExpansionLineage.ORIGINAL)));
    }

    /**
     * The site of one construct answering a truth, or the fact that this run has no site for it.
     *
     * <p>Matched on the construct the source wrote, for the reason {@link #armOf} gives. A
     * construct is a comparison or an application and never both, so it is found among one.
     */
    private static DecisionRuleReading outcomeOf(CoverageSites.Plan plan, String behavior,
                                                 ModelOccurrence construct, boolean held) {
        for (CoverageSites.ComparisonSite site : plan.comparisons(behavior)) {
            if (site.obligation().origin().equals(construct.origin())) {
                return new AComparisonCameOut(site, held, construct.lineage());
            }
        }
        for (CoverageSites.AnswerSite site : plan.answers(behavior)) {
            if (site.application().origin().equals(construct.origin())) {
                return new AnApplicationAnswered(site, held, construct.lineage());
            }
        }
        return new AnOutcomeIsNotPlaced(construct, held);
    }

    /**
     * The site of one arm of one fork, or the fact that this run has no site for it.
     *
     * <p>Matched on the construct the source wrote, which is what the two trees agree about. A
     * helper carrying a fork stands in the running tree once per call site and those differ in
     * their lineage, while the arm a row is owed for is the construct — so an occurrence is the
     * wrong grain to match on here and would find nothing for the copies. Which copy it was is
     * kept beside the site rather than matched on.
     */
    private static DecisionRuleReading armOf(CoverageSites.Plan plan, String behavior,
                                             ModelOccurrence fork, int part) {
        for (CoverageSites.ArmSite site : plan.arms(behavior)) {
            if (site.obligation().part() == part
                    && site.obligation().origin().equals(fork.origin())) {
                return new AForkTookAnArm(site, fork.lineage());
            }
        }
        return new AForkIsNotPlaced(fork, part);
    }
}
