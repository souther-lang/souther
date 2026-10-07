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
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * Which rule of a body's decision each run took.
 *
 * <p>What discharges a decision rule is a row whose evaluation takes that path, so this is where a
 * run and a rule meet. The rule is read off the tree the language's operations stand in and the run
 * is recorded where they are expanded; what the two agree about is the construct of the model, and
 * the plan says where the emitter numbered each one.
 *
 * <p><b>A rule is taken where every condition on its path was seen coming out the way the rule
 * says.</b> Not where some of them were: the conditions of a path are what makes it that path, and
 * a run that matched all but one took a different one.
 *
 * <p><b>And a rule no run can be recognised at is not refuted by any run.</b> A path carrying a
 * condition with no construct of the model to be seen at, or one the emitter numbered no site for,
 * is one this compiler cannot tell a run took — so it is set aside rather than answered no, which
 * would report the rules a body has as rules its rows never reach.
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
            /** More than one rule matched, which one run cannot have done. */
            MORE_THAN_ONE_RULE_MATCHES
        }
    }

    /**
     * One rule and what a run through it has to be seen doing.
     *
     * <p>Each condition of the path is one thing to have been seen, and a condition materialised
     * more than once in the tree that runs is seen at whichever of them the run passed — a helper
     * carrying a fork is expanded per call site, and a row through any of those copies went through
     * the arm the model states.
     */
    private record Recognised(DecisionRule rule, List<Seen> conditions) {

        boolean satisfiedBy(AlignedObservation seen) {
            for (Seen each : conditions) {
                if (!each.satisfiedBy(seen)) {
                    return false;
                }
            }
            return true;
        }
    }

    /** What a run through one condition of a rule has to be seen doing. */
    private sealed interface Seen {

        boolean satisfiedBy(AlignedObservation seen);

        /** Recorded at one of these: each a materialisation of the one place. */
        record AtAnyOf(List<ControlClaim> alternatives) implements Seen {

            @Override
            public boolean satisfiedBy(AlignedObservation seen) {
                for (ControlClaim each : alternatives) {
                    if (each.satisfiedBy(seen)) {
                        return true;
                    }
                }
                return false;
            }
        }

        /**
         * Down one of the materialisations of an arm, and at none of the places an operand is
         * recorded at — every materialisation of it, since a run that reached any copy of the
         * operand is one this cannot say stopped short of it.
         */
        record DownAnArmShortOf(List<ControlClaim> arm, List<ConditionOutcomeSite> notReached)
                implements Seen {

            @Override
            public boolean satisfiedBy(AlignedObservation seen) {
                if (!new AtAnyOf(arm).satisfiedBy(seen)) {
                    return false;
                }
                for (ConditionOutcomeSite each : notReached) {
                    if (seen.reached(each)) {
                        return false;
                    }
                }
                return true;
            }
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
            List<Seen> conditions = new ArrayList<>();
            boolean everyOne = true;
            for (ShownBy each : ruled.shownBy()) {
                Optional<Seen> seen = seenAs(each, comparisons, answers, arms, plan);
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
     * What a run through one condition of a path is seen doing, or empty where this compiler
     * cannot recognise a run through it.
     *
     * <p>Empty is one answer over several causes: the condition has no construct of the model, the
     * emitted tree holds no materialisation of that construct, and the plan numbered no site for the
     * ones it holds. None of them is anything about the model, so they arrive here as one.
     */
    private static Optional<Seen> seenAs(ShownBy shown, ComparisonEmissionIndex comparisons,
                                         AnswerEmissionIndex answers, ArmEmissionIndex arms,
                                         CoverageSites.Plan plan) {
        return switch (shown) {
            case ShownBy.AtAnOutcome at -> some(new Seen.AtAnyOf(
                    outcomes(at.construct(), at.held(), comparisons, answers, plan)));
            case ShownBy.AtAnArm at -> some(new Seen.AtAnyOf(armOf(at.fork(), at.part(), arms)));
            // Short of the operand at every place it is recorded, each copy of it both ways: a copy
            // the plan records no run through is one a run may have reached, and with it this
            // cannot say the run stopped short.
            case ShownBy.AtAnArmShortOf at -> {
                List<ControlClaim> arm = armOf(at.fork(), at.part(), arms);
                List<ConditionOutcomeSite> sites = new ArrayList<>();
                int copies = comparisons.madeFor(at.notReached()).size()
                        + answers.madeFor(at.notReached()).size();
                for (ControlClaim each : outcomes(at.notReached(), true, comparisons, answers,
                        plan)) {
                    if (each.at() instanceof ControlPlace.Outcome outcome) {
                        sites.add(outcome.at());
                    }
                }
                yield arm.isEmpty() || sites.isEmpty() || sites.size() != copies
                        ? Optional.empty()
                        : Optional.of(new Seen.DownAnArmShortOf(arm, List.copyOf(sites)));
            }
            case ShownBy.ShortOf _, ShownBy.NothingIsRecorded _ -> Optional.empty();
        };
    }

    /** {@code seen}, where it has a place to be seen at. */
    private static Optional<Seen> some(Seen.AtAnyOf seen) {
        return seen.alternatives().isEmpty() ? Optional.empty() : Optional.of(seen);
    }

    /**
     * Where {@code construct} coming out {@code held} is recorded, one entry per materialisation
     * the emitter numbered.
     *
     * <p>A construct of the model is a comparison or an application and never both, so it is
     * looked for among the copies of each and found among one.
     */
    private static List<ControlClaim> outcomes(ModelOccurrence construct, boolean held,
                                               ComparisonEmissionIndex comparisons,
                                               AnswerEmissionIndex answers,
                                               CoverageSites.Plan plan) {
        List<ControlClaim> out = new ArrayList<>();
        for (ComparisonEmissionIndex.EmittedComparison made : comparisons.madeFor(construct)) {
            // Asked of the plan, which is the one maker of a place a comparison comes out one
            // way: it takes the address for the comparison being asked about, so the two are one
            // answer rather than a pair assembled here.
            plan.outcomeOf(made.occurrence(), held).flatMap(ControlClaim::of).ifPresent(out::add);
        }
        for (CoverageSites.AnswerSite made : answers.madeFor(construct)) {
            plan.outcomeOf(made.application(), held).flatMap(ControlClaim::of)
                    .ifPresent(out::add);
        }
        return List.copyOf(out);
    }

    /** Where a run down arm {@code part} of {@code fork} is recorded, one entry per
     *  materialisation. */
    private static List<ControlClaim> armOf(ModelOccurrence fork, int part, ArmEmissionIndex arms) {
        List<ControlClaim> out = new ArrayList<>();
        for (ControlPlace.Arm arm : arms.madeFor(new ArmEmissionIndex.ArmOfTheModel(fork, part))) {
            ControlClaim.of(arm).ifPresent(out::add);
        }
        return List.copyOf(out);
    }

    /** Which rule {@code seen} took. */
    public WhichRule takenBy(AlignedObservation seen) {
        if (recognisable.isEmpty()) {
            return new WhichRule.CouldNotTell(WhichRule.Why.NO_RULE_IS_RECOGNISABLE);
        }
        DecisionRule took = null;
        for (Recognised each : recognisable) {
            if (!each.satisfiedBy(seen)) {
                continue;
            }
            if (took != null) {
                return new WhichRule.CouldNotTell(WhichRule.Why.MORE_THAN_ONE_RULE_MATCHES);
            }
            took = each.rule();
        }
        return took == null
                ? new WhichRule.CouldNotTell(WhichRule.Why.NO_RECOGNISABLE_RULE_MATCHES)
                : new WhichRule.TookThis(took);
    }
}
