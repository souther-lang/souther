package souther.compiler.query;

import souther.compiler.coverage.ArmReportAnchor;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.partition.DecisionCondition;
import souther.compiler.partition.ShownBy;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.StepOfACopy;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
 *
 * <p><b>Which copy, as it was read.</b> A construct is one site however many copies of it stand in
 * the tree, so each reading carries the steps of the copy it is of. A rule's are the calls of the
 * model the rule names its construct under; a combination's are every step of the occurrence the
 * run is recorded at, taken as the measure holds it and never rebuilt from a projection of it.
 */
public sealed interface DecisionRuleReading {

    /**
     * The steps of the copy this condition is of, outermost first, and none where it stands where
     * it is written or where there is no construct to be a copy of.
     */
    List<StepOfACopy> through();

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
     * @param through    which copy of it ({@link DecisionRuleReading#through})
     */
    record AComparisonCameOut(CoverageSites.ComparisonSite comparison, boolean held,
                              List<StepOfACopy> through) implements DecisionRuleReading {

        public AComparisonCameOut {
            Objects.requireNonNull(comparison, "a comparison of the model is some site");
            through = List.copyOf(through);
        }
    }

    /**
     * An application of one of the language's operations the author wrote, answering one way.
     *
     * @param application where the code answering it stands, which is what a reader is sent to
     * @param held        whether the path took it answering true
     * @param through     which copy of it ({@link DecisionRuleReading#through})
     */
    record AnApplicationAnswered(CoverageSites.AnswerSite application, boolean held,
                                 List<StepOfACopy> through) implements DecisionRuleReading {

        public AnApplicationAnswered {
            Objects.requireNonNull(application, "an application of the model is some site");
            through = List.copyOf(through);
        }
    }

    /**
     * A construct answering a truth — a comparison or an application — that this run has no site
     * for.
     *
     * <p>Beside {@link AConditionIsNotShown} for the reason {@link AForkIsNotPlaced} is: this is
     * the plan that numbered the places having nothing under the construct the reading named,
     * rather than the reading of the body falling short of saying what a condition means.
     */
    record AnOutcomeIsNotPlaced(SourceConstructOrigin construct, boolean held,
                                List<StepOfACopy> through) implements DecisionRuleReading {

        public AnOutcomeIsNotPlaced {
            Objects.requireNonNull(construct, "a truth is some construct's");
            through = List.copyOf(through);
        }
    }

    /**
     * A fork, with the path going down one of its arms.
     *
     * <p>The site and not the fork and a number. Which arm a reader is told about is a thing the
     * coverage sites already have words for, and a sentence built from the number would be a second
     * naming of one arm, free to call it something the branch account does not.
     *
     * @param arm     which arm, which is what a reader is told it is
     * @param shownAt where a reader is sent for it. The site's own for a rule, which names the
     *                construct of the model; the place the run is recorded at for a combination,
     *                which names the copy — an arm inside one of the language's own operations is
     *                shown at the call that reached it, and a site made for the first such call
     *                would send a reader of the second to the first
     * @param through which copy of the fork ({@link DecisionRuleReading#through}). The site is one
     *                per construct, and a value called twice is one construct standing in two
     *                places — a path through both copies, one each way, said by the sites alone
     *                reads the same as the path the other way round
     */
    record AForkTookAnArm(CoverageSites.ArmSite arm, ArmReportAnchor shownAt,
                          List<StepOfACopy> through) implements DecisionRuleReading {

        public AForkTookAnArm {
            Objects.requireNonNull(arm, "an arm of the model is some site");
            Objects.requireNonNull(shownAt, "an arm is shown somewhere");
            through = List.copyOf(through);
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

        @Override
        public List<StepOfACopy> through() {
            return List.of();
        }
    }

    /**
     * A fork this run has no site for.
     *
     * <p>Beside {@link AConditionIsNotShown} and not among it. That one is the reading of the body
     * falling short of saying what a condition means; this is the plan that numbered the places
     * having nothing under the construct the reading named — a different thing to chase, and a
     * reader told the first would go looking for a shape this compiler cannot read.
     */
    record AForkIsNotPlaced(SourceConstructOrigin fork, int part, List<StepOfACopy> through)
            implements DecisionRuleReading {

        public AForkIsNotPlaced {
            Objects.requireNonNull(fork, "an arm is an arm of some fork");
            through = List.copyOf(through);
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
                                        Places places) {
        List<DecisionRuleReading> out = new ArrayList<>();
        for (ShownBy each : ruled.shownBy()) {
            out.add(switch (each) {
                case ShownBy.AtAnOutcome(var construct, var held) ->
                        places.outcomeOf(construct.origin(), held, stepsOf(construct));
                case ShownBy.AtAnArm(var fork, var part) -> places.armOf(fork.origin(), part,
                        stepsOf(fork), null);
                // The arm is the place a reader is sent to: the operand not run is what the run
                // there did not do, and there is no place to send anyone for that.
                case ShownBy.AtAnArmShortOf(var fork, var part, var _) ->
                        places.armOf(fork.origin(), part, stepsOf(fork), null);
                case ShownBy.ShortOf(var condition, var _) -> new AConditionIsNotShown(condition);
                case ShownBy.NothingIsRecorded(var condition) ->
                        new AConditionIsNotShown(condition);
            });
        }
        return List.copyOf(out);
    }

    /** The calls of the model {@code construct} stands in. */
    private static List<StepOfACopy> stepsOf(ModelOccurrence construct) {
        return StepOfACopy.of(construct.lineage());
    }

    /**
     * What a run that came one way to a combination of a body's decisions would be seen doing, one
     * reading per place, in the order the way holds them.
     *
     * <p>Read off the places and not off the decisions the combination is told apart by. Those are
     * held in the terms a search steers a row by, and a sentence made of them would name input
     * positions the way this compiler spells them; the places are the comparisons, applications and
     * arms the author wrote, each found by the construct it is of.
     *
     * <p>Which copy, and where an arm is shown, are the claim's own. The claim is the occurrence a
     * run is recorded at, every step of it — the calls of the model, a call of one of the
     * language's own operations, a build — and a reading that kept less would say two places a run
     * is recorded at in one sentence.
     *
     * <p>A copy of a construct said once. One arm can stand for several conditions — a run down it
     * brought every truth of the condition out the way the arm says — and a sentence for each would
     * be the same sentence.
     */
    static List<DecisionRuleReading> ofAWay(List<ControlClaim> claims, Places places) {
        Set<DecisionRuleReading> out = new LinkedHashSet<>();
        for (ControlClaim claim : claims) {
            out.add(switch (claim.at()) {
                case ControlPlace.Outcome(var occurrence, var _, var held) ->
                        places.outcomeOf(occurrence.origin(), held,
                                StepOfACopy.of(occurrence.lineage()));
                case ControlPlace.Arm(var arm, var _, var anchor) ->
                        places.armOf(arm.origin(), arm.part(),
                                StepOfACopy.of(arm.fork().lineage()), anchor);
            });
        }
        return List.copyOf(out);
    }

    /**
     * The sites of one behavior a reading resolves its conditions against, filed by the construct
     * of the source each is a site of.
     *
     * <p>Filed once and asked once per condition. The plan answers a behavior's sites as a list
     * made afresh on every asking, each site owed to the behavior anew, and a reading that walked
     * that list for each condition paid for every site of the module once per condition of every
     * rule and combination it read. Where one construct has more than one site, the first is the
     * one filed, which is the one a walk of the list would have stopped at.
     */
    public static final class Places {

        private final Map<SourceConstructOrigin, CoverageSites.ComparisonSite> comparisons =
                new HashMap<>();
        private final Map<SourceConstructOrigin, CoverageSites.AnswerSite> answers =
                new HashMap<>();
        private final Map<ArmOf, CoverageSites.ArmSite> arms = new HashMap<>();

        /** One arm of one fork of the source. */
        private record ArmOf(SourceConstructOrigin fork, int part) {}

        private Places(CoverageSites.Plan plan, String behavior) {
            for (CoverageSites.ComparisonSite site : plan.comparisons(behavior)) {
                comparisons.putIfAbsent(site.obligation().origin(), site);
            }
            for (CoverageSites.AnswerSite site : plan.answers(behavior)) {
                answers.putIfAbsent(site.application().origin(), site);
            }
            for (CoverageSites.ArmSite site : plan.arms(behavior)) {
                arms.putIfAbsent(new ArmOf(site.obligation().origin(), site.obligation().part()),
                        site);
            }
        }

        /** The sites of {@code behavior} that {@code plan} numbered. */
        public static Places of(CoverageSites.Plan plan, String behavior) {
            return new Places(plan, behavior);
        }

        /**
         * The site of one construct answering a truth, or the fact that this run has no site for
         * it.
         *
         * <p>Matched on the construct the source wrote, for the reason {@link #armOf} gives. A
         * construct is a comparison or an application and never both, so it is found among one.
         */
        DecisionRuleReading outcomeOf(SourceConstructOrigin construct, boolean held,
                                      List<StepOfACopy> through) {
            CoverageSites.ComparisonSite comparison = comparisons.get(construct);
            if (comparison != null) {
                return new AComparisonCameOut(comparison, held, through);
            }
            CoverageSites.AnswerSite answer = answers.get(construct);
            if (answer != null) {
                return new AnApplicationAnswered(answer, held, through);
            }
            return new AnOutcomeIsNotPlaced(construct, held, through);
        }

        /**
         * The site of one arm of one fork, or the fact that this run has no site for it.
         *
         * <p>Matched on the construct the source wrote, which is what the two trees agree about. A
         * helper carrying a fork stands in the running tree once per call site and those differ in
         * their lineage, while the arm a row is owed for is the construct — so an occurrence is the
         * wrong grain to match on here and would find nothing for the copies. Which copy it was is
         * kept beside the site rather than matched on.
         *
         * @param shownAt where a reader is sent for it, or null for the site's own
         */
        DecisionRuleReading armOf(SourceConstructOrigin fork, int part, List<StepOfACopy> through,
                                  ArmReportAnchor shownAt) {
            CoverageSites.ArmSite site = arms.get(new ArmOf(fork, part));
            return site == null ? new AForkIsNotPlaced(fork, part, through)
                    : new AForkTookAnArm(site, shownAt == null ? site.anchor() : shownAt,
                            through);
        }
    }
}
