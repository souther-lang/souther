package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.AnswerEmissionIndex;
import souther.compiler.coverage.ArmEmissionIndex;
import souther.compiler.coverage.ComparisonEmissionIndex;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * Which rule of a body's decision each run took.
 *
 * <p>What discharges a decision rule is a row whose evaluation takes that path, so this is where a
 * run and a rule meet. The rule is read off the tree the language's operations stand in and the run
 * is recorded where they are expanded; what the two agree about is the construct of the model, and
 * the plan says where the emitter numbered each one.
 *
 * <p>Two things apart, and joined only here. Where a run through a condition of a rule is recorded
 * is a fact about the body and the plan ({@link ColumnWitness}); what one run was recorded doing at
 * those places is a fact about the run ({@link ExecutionEvidence}). Neither is worked out from the
 * other.
 *
 * <p><b>A rule is taken where every condition on its path was seen coming out the way the rule
 * says, and no other way.</b> Not where some of them were: the conditions of a path are what makes
 * it that path, and a run that matched all but one took a different one. And a condition a run was
 * recorded answering both ways — a fork it passed more than once — is not a value of that run: the
 * run went down more than one path through it, and which one this row stands in is not something
 * the records say.
 *
 * <p><b>And a rule no run can be recognised at is not refuted by any run.</b> A path carrying a
 * condition with no construct of the model to be seen at, or one the emitter numbered no site for,
 * is one this compiler cannot tell a run took — so it is set aside rather than answered no, which
 * would report the rules a body has as rules its rows never reach. A truth the body was handed
 * and passed on is the one condition of that kind a run is still seen at: the row wrote the value,
 * and the position it wrote it at is a position of the declared inputs.
 *
 * <p>A rule that is not {@link DecisionReading.Ruled#whole} is set aside too. Its path carries fewer
 * conditions than its way turns on, so a run matching every condition it carries has not been shown
 * to have taken it — and a path with none left is matched by every run. A path with no conditions
 * that is whole is another thing: a body that draws no distinction has one rule, and every run
 * takes it.
 */
public final class RulesTaken {

    /**
     * Which rule a run took, or that this compiler could not tell.
     *
     * <p>Three answers rather than two, because what a reader does with them differs. A run whose
     * rule is known is evidence that something stands there; a run whose rule could not be told is
     * this compiler falling short and says nothing about the model; and a run matching no rule at
     * all is the reading and the run disagreeing about the body, which is worth knowing.
     */
    public sealed interface WhichRule {

        /** The rule this run took. */
        record TookThis(DecisionRule rule) implements WhichRule {}

        /** No rule this reading can recognise a run at matched, and why that is not a fact about
         *  the model. */
        record CouldNotTell(Why why) implements WhichRule {}

        /** Why a run's rule could not be told. */
        enum Why {
            /** Every rule of the body carries a condition no run through it is recorded at, or was
             *  read with fewer conditions than its way turns on. */
            NO_RULE_IS_RECOGNISABLE,
            /** The rules that can be recognised were each missing something the run did not do. */
            NO_RECOGNISABLE_RULE_MATCHES,
            /** A rule would have matched but for a condition the run was recorded answering both
             *  ways, which says it went down more than one path there. */
            A_CONDITION_CAME_OUT_BOTH_WAYS,
            /** More than one rule matched, which one run cannot have done. */
            MORE_THAN_ONE_RULE_MATCHES
        }
    }

    /**
     * What one run was recorded doing at the places one condition of a rule is seen at.
     *
     * <p>Four answers and not a yes or a no. A condition the run answered the other way and one it
     * never reached both leave the rule untaken, and they are different things to have seen; one it
     * answered both ways is the run having gone down more than one path, which is neither.
     */
    enum ExecutionEvidence {
        AS_THE_RULE_SAYS,
        THE_OTHER_WAY,
        BOTH_WAYS,
        UNOBSERVED;

        static ExecutionEvidence of(boolean asTheRuleSays, boolean theOtherWay) {
            if (asTheRuleSays) {
                return theOtherWay ? BOTH_WAYS : AS_THE_RULE_SAYS;
            }
            return theOtherWay ? THE_OTHER_WAY : UNOBSERVED;
        }
    }

    /**
     * Where a run through one condition of a rule is recorded, both the way the rule takes it and
     * the other ways it could go.
     *
     * <p>Each condition is seen at every materialisation of the construct of the model it is: a
     * helper carrying a fork is expanded per call site, and a row through any of those copies went
     * through the arm the model states. The ways it did not take are held beside the way it did, so
     * that a run that went both ways is told from one that went the rule's way.
     */
    private sealed interface ColumnWitness {

        ExecutionEvidence in(Run run);

        /** A construct answering a truth, at each place it is recorded. */
        record AtOutcomes(Set<ConditionOutcomeSite> sites, boolean held) implements ColumnWitness {

            @Override
            public ExecutionEvidence in(Run run) {
                boolean asTheRuleSays = false;
                boolean theOtherWay = false;
                for (ConditionOutcomeSite each : sites) {
                    asTheRuleSays |= run.seen().saw(each, held);
                    theOtherWay |= run.seen().saw(each, !held);
                }
                return ExecutionEvidence.of(asTheRuleSays, theOtherWay);
            }
        }

        /**
         * A truth the body was handed and passed on, which no construct answers and so no run is
         * recorded at: the value the row wrote at the position is the whole of what there is to see.
         *
         * <p>Only a position the declared inputs walk to one value at. A position the walk does not
         * reach, or reaches several values at, is a condition this has seen nothing of, and not one
         * the row answered the other way.
         */
        record AtAnInputTruth(TermPath at, boolean held) implements ColumnWitness {

            @Override
            public ExecutionEvidence in(Run run) {
                if (run.inputs().indexOf(at) < 0
                        || run.inputs().indexOf(at) >= run.values().size()) {
                    return ExecutionEvidence.UNOBSERVED;
                }
                if (run.inputs().valuesAt(run.values(), at)
                        instanceof WalkResult.Reached<List<ObservedValue>>(var found)
                        && found.size() == 1
                        && found.getFirst() instanceof ObservedValue.Bool it) {
                    return it.value() == held ? ExecutionEvidence.AS_THE_RULE_SAYS
                            : ExecutionEvidence.THE_OTHER_WAY;
                }
                return ExecutionEvidence.UNOBSERVED;
            }
        }

        /** An arm of a fork, at each materialisation of it, beside every other arm of the fork. */
        record AtArms(Set<ControlClaim> arm, Set<ControlClaim> besides) implements ColumnWitness {

            @Override
            public ExecutionEvidence in(Run run) {
                return ExecutionEvidence.of(anyOf(arm, run.seen()), anyOf(besides, run.seen()));
            }

            private static boolean anyOf(Set<ControlClaim> claims, AlignedObservation seen) {
                for (ControlClaim each : claims) {
                    if (each.satisfiedBy(seen)) {
                        return true;
                    }
                }
                return false;
            }
        }

        /**
         * Down an arm, and at none of the places an operand is recorded at — every materialisation
         * of it, since a run that reached any copy of the operand is one this cannot say stopped
         * short of it.
         */
        record DownAnArmShortOf(AtArms arm, Set<ConditionOutcomeSite> notReached)
                implements ColumnWitness {

            @Override
            public ExecutionEvidence in(Run run) {
                ExecutionEvidence down = arm.in(run);
                if (down != ExecutionEvidence.AS_THE_RULE_SAYS) {
                    return down;
                }
                for (ConditionOutcomeSite each : notReached) {
                    if (run.seen().reached(each)) {
                        return ExecutionEvidence.THE_OTHER_WAY;
                    }
                }
                return ExecutionEvidence.AS_THE_RULE_SAYS;
            }
        }
    }

    /**
     * One run as the conditions of a rule are read off it: where it went, and the values it was
     * given, which are read at the positions the declared inputs name.
     */
    private record Run(AlignedObservation seen, List<ObservedValue> values,
                       BehaviorInputs inputs) {}

    /** One rule and where each condition of its path is recorded. */
    private record Recognised(DecisionRule rule, List<ColumnWitness> conditions) {

        /** What {@code run} shows of each condition, in the order of the path. */
        List<ExecutionEvidence> in(Run run) {
            List<ExecutionEvidence> out = new ArrayList<>();
            for (ColumnWitness each : conditions) {
                out.add(each.in(run));
            }
            return out;
        }
    }

    private final List<Recognised> recognisable;

    private RulesTaken(List<Recognised> recognisable) {
        this.recognisable = recognisable;
    }

    /**
     * Two of these are one where they recognise the same runs at the same rules.
     *
     * <p>Said because this is an answer of the query graph, and an answer that says nothing of
     * itself is one nothing can tell from a second computation of the same question — which is how
     * a memoised graph loses the guarantee it exists to give. Everything it is made of is a value,
     * so what it is made of is what it is.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof RulesTaken it && recognisable.equals(it.recognisable);
    }

    @Override
    public int hashCode() {
        return recognisable.hashCode();
    }

    /**
     * The rules of {@code read}, against the tree that runs and the plan that numbered it.
     *
     * <p>Both trees are asked for because the crossing is about the pair: the rules say which
     * constructs of the model they turn on, and the plan says which of those a run is recorded at.
     */
    public static RulesTaken of(DecisionReading read, Core emitted, CoverageSites.Plan plan) {
        ComparisonEmissionIndex comparisons = ComparisonEmissionIndex.ofBody(emitted, plan);
        AnswerEmissionIndex answers = AnswerEmissionIndex.ofBody(emitted, plan);
        ArmEmissionIndex arms = ArmEmissionIndex.ofBody(emitted, plan);
        List<Recognised> recognisable = new ArrayList<>();
        for (DecisionReading.Ruled ruled : read.found()) {
            if (!ruled.whole()) {
                continue;
            }
            List<ColumnWitness> conditions = new ArrayList<>();
            boolean everyOne = true;
            for (ShownBy each : ruled.shownBy()) {
                Optional<ColumnWitness> seen =
                        witnessOf(each, ruled.rule(), comparisons, answers, arms, plan);
                everyOne &= seen.isPresent();
                seen.ifPresent(conditions::add);
            }
            if (everyOne) {
                recognisable.add(new Recognised(ruled.rule(), List.copyOf(conditions)));
            }
        }
        return new RulesTaken(List.copyOf(recognisable));
    }

    /**
     * Where a run through one condition of a path is recorded, or empty where this compiler cannot
     * recognise a run through it.
     *
     * <p>Empty is one answer over several causes: the condition has no construct of the model, the
     * emitted tree holds no materialisation of that construct, and the plan numbered no site for the
     * ones it holds. None of them is anything about the model, so they arrive here as one.
     */
    private static Optional<ColumnWitness> witnessOf(ShownBy shown,
                                                     DecisionRule rule,
                                                     ComparisonEmissionIndex comparisons,
                                                     AnswerEmissionIndex answers,
                                                     ArmEmissionIndex arms,
                                                     CoverageSites.Plan plan) {
        return switch (shown) {
            case ShownBy.AtAnOutcome at -> {
                Set<ConditionOutcomeSite> sites =
                        outcomes(at.construct(), comparisons, answers, plan);
                yield sites.isEmpty() ? Optional.empty()
                        : Optional.of(new ColumnWitness.AtOutcomes(sites, at.held()));
            }
            case ShownBy.AtAnArm at ->
                    armOf(at.fork(), at.part(), arms).map(ColumnWitness.class::cast);
            // Short of the operand at every place it is recorded: a copy the plan records no run
            // through is one a run may have reached, and with it this cannot say the run stopped
            // short.
            case ShownBy.AtAnArmShortOf at -> {
                Optional<ColumnWitness.AtArms> arm = armOf(at.fork(), at.part(), arms);
                Set<ConditionOutcomeSite> sites =
                        outcomes(at.notReached(), comparisons, answers, plan);
                int copies = comparisons.madeFor(at.notReached()).size()
                        + answers.madeFor(at.notReached()).size();
                yield arm.isEmpty() || sites.isEmpty() || sites.size() != copies
                        ? Optional.empty()
                        : Optional.of(new ColumnWitness.DownAnArmShortOf(arm.get(), sites));
            }
            // Only a truth that is an input position itself. Any other condition nothing records is
            // not read off the values, which would be evaluating the body a second time.
            case ShownBy.NothingIsRecorded(var condition) -> switch (rule.at(condition)) {
                case DecidedCondition.Stood(
                        DecisionCondition.ATruth(DecisionSubject.AnInput(var at)), var held) ->
                        Optional.of(new ColumnWitness.AtAnInputTruth(at, held));
                case null, default -> Optional.empty();
            };
            case ShownBy.ShortOf _ -> Optional.empty();
        };
    }

    /**
     * Where {@code construct} answering is recorded, one site per materialisation the emitter
     * numbered.
     *
     * <p>A construct of the model is a comparison or an application and never both, so it is
     * looked for among the copies of each and found among one. Asked of the plan, which is the one
     * maker of a place a construct comes out one way; a site is the same place whichever way it
     * came out there.
     */
    private static Set<ConditionOutcomeSite> outcomes(ModelOccurrence construct,
                                                      ComparisonEmissionIndex comparisons,
                                                      AnswerEmissionIndex answers,
                                                      CoverageSites.Plan plan) {
        Set<ConditionOutcomeSite> out = new HashSet<>();
        for (ComparisonEmissionIndex.EmittedComparison made : comparisons.madeFor(construct)) {
            plan.outcomeOf(made.occurrence(), true).map(ControlPlace.Outcome::at)
                    .ifPresent(out::add);
        }
        for (CoverageSites.AnswerSite made : answers.madeFor(construct)) {
            plan.outcomeOf(made.application(), true).map(ControlPlace.Outcome::at)
                    .ifPresent(out::add);
        }
        return Set.copyOf(out);
    }

    /**
     * Where a run down arm {@code part} of {@code fork} is recorded, beside where a run down any
     * other arm of it is, or empty where no materialisation of the arm has a place to be seen at.
     */
    private static Optional<ColumnWitness.AtArms> armOf(ModelOccurrence fork, int part,
                                                       ArmEmissionIndex arms) {
        ArmEmissionIndex.ArmOfTheModel which = new ArmEmissionIndex.ArmOfTheModel(fork, part);
        Set<ControlClaim> arm = claims(arms.madeFor(which));
        return arm.isEmpty() ? Optional.empty()
                : Optional.of(new ColumnWitness.AtArms(arm, claims(arms.besides(which))));
    }

    private static Set<ControlClaim> claims(Iterable<ControlPlace.Arm> places) {
        Set<ControlClaim> out = new HashSet<>();
        for (ControlPlace.Arm each : places) {
            ControlClaim.of(each).ifPresent(out::add);
        }
        return Set.copyOf(out);
    }

    /**
     * Which rule a run took, given where it went and the values it was given.
     *
     * <p>Takes the run's account and not whether there is one: a row nothing watched took no rule
     * this can name, and a caller holding one says so before asking.
     *
     * <p>The declared inputs are asked of rather than held, since this is an answer of the query
     * graph and what they are made of compares by identity.
     *
     * @param values what the row wrote, one per parameter, or empty where they were not read, which
     *               leaves every truth read off them unobserved
     * @param inputs what the behavior takes, which says where in {@code values} a position is
     */
    public WhichRule takenBy(AlignedObservation seen, List<ObservedValue> values,
                             BehaviorInputs inputs) {
        if (recognisable.isEmpty()) {
            return new WhichRule.CouldNotTell(WhichRule.Why.NO_RULE_IS_RECOGNISABLE);
        }
        Run run = new Run(seen, values, inputs);
        DecisionRule took = null;
        boolean butForBothWays = false;
        for (Recognised each : recognisable) {
            List<ExecutionEvidence> evidence = each.in(run);
            if (evidence.stream().allMatch(ExecutionEvidence.AS_THE_RULE_SAYS::equals)) {
                if (took != null) {
                    return new WhichRule.CouldNotTell(WhichRule.Why.MORE_THAN_ONE_RULE_MATCHES);
                }
                took = each.rule();
            } else if (evidence.stream().allMatch(it -> it == ExecutionEvidence.AS_THE_RULE_SAYS
                    || it == ExecutionEvidence.BOTH_WAYS)) {
                butForBothWays = true;
            }
        }
        if (took != null) {
            return new WhichRule.TookThis(took);
        }
        return new WhichRule.CouldNotTell(butForBothWays
                ? WhichRule.Why.A_CONDITION_CAME_OUT_BOTH_WAYS
                : WhichRule.Why.NO_RECOGNISABLE_RULE_MATCHES);
    }
}
