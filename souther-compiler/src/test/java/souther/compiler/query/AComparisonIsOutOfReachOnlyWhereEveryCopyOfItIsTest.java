package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.check.PathReachability;
import souther.compiler.core.Core;
import souther.compiler.coverage.ComparisonEmissionIndex;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.SourcePos;
import souther.compiler.partition.AnswersDemanded;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.RuleStep;
import souther.compiler.partition.SaidOnTheWay;
import souther.compiler.partition.ShownBy;
import souther.compiler.query.Adequacy.DecisionSearch.NothingReaches;
import souther.compiler.reach.PathDecision;
import souther.compiler.reach.Proof;
import souther.compiler.reach.Reachability;
import souther.compiler.reach.WhyUnsettled;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A rule's way is out by a comparison only where every copy of that comparison the tree that runs
 * holds was proven to come out the way nowhere, and wherever the way is seen at it.
 *
 * <p>{@code x > 0} is written once, inside the key handed to {@code List.distinctBy}, and the tree
 * that runs evaluates it at two places. A proof about one of them says nothing about the other — a
 * run may come out that way at the second — so what the reading of reach answers at each copy is
 * set here by hand, over the plan and the copies the compile made, and the question is put to the
 * one reader that turns those answers into a rule left out.
 */
class AComparisonIsOutOfReachOnlyWhereEveryCopyOfItIsTest {

    private static final String MODEL = """
            module m

            data Low
            data High

            behavior pick : (xs: List<Int>) -> Low | High
            let pick (xs) =
                if List.length(List.distinctBy(x -> x > 0, xs)) > 1 then High else Low
            """;

    private static final Compiled COMPILED = compiled();

    @Test
    void oneCopyLeftOpenKeepsTheRuleIn() {
        NothingReaches reading = with(Map.of(
                COMPILED.twice().get(0), unreachable(), COMPILED.twice().get(1), unsettled()));

        assertNull(reading.onTheWay(seenAt(at(COMPILED.writtenTwice()))),
                "a run may bring the key's comparison out true at the copy nothing was proven of");
    }

    @Test
    void everyCopyProvenTakesTheRuleOut() {
        NothingReaches reading = with(Map.of(
                COMPILED.twice().get(0), unreachable(), COMPILED.twice().get(1), unreachable()));

        assertEquals(new RuleRequirement.Excluded.AComparisonOutcomeNothingReaches(
                        COMPILED.writtenTwice(), true),
                reading.onTheWay(seenAt(at(COMPILED.writtenTwice()))));
    }

    /** No copy proven of at all is the same answer as one left open, and the control for both
     *  above: an answer of nothing proven leaves every rule in. */
    @Test
    void nothingProvenKeepsTheRuleIn() {
        NothingReaches reading = with(Map.of());

        assertNull(reading.onTheWay(seenAt(at(COMPILED.writtenTwice()))));
    }

    /**
     * A step met at several places is passed at each, so the way is out by any of them — and the
     * one out here is the second place the step is seen at, with the first left open.
     */
    @Test
    void everyPlaceAStepIsSeenAtIsAsked() {
        NothingReaches reading = with(Map.of(
                COMPILED.twice().get(0), unreachable(), COMPILED.twice().get(1), unreachable(),
                COMPILED.once(), unsettled()));

        assertEquals(new RuleRequirement.Excluded.AComparisonOutcomeNothingReaches(
                        COMPILED.writtenTwice(), true),
                reading.onTheWay(seenAt(at(COMPILED.writtenOnce()),
                        at(COMPILED.writtenTwice()))));
    }

    // --- what the compile made, and answers put over it --------------------------------------------

    /**
     * The plan and the copies, and the reading of reach the compile made.
     *
     * @param writtenTwice the key's comparison, as the model writes it
     * @param twice        where each of its two copies comes out true
     * @param writtenOnce  the fork's own comparison
     * @param once         where its one copy comes out true
     * @param where        somewhere in the body, for a proof set by hand to name
     */
    private record Compiled(CoverageSites.Plan plan, ComparisonEmissionIndex copies,
                            PathReachability.Answers answers,
                            ModelOccurrence writtenTwice, List<ControlPlace.Outcome> twice,
                            ModelOccurrence writtenOnce, ControlPlace.Outcome once,
                            SourcePos where) {}

    private static Compiled compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        Core emitted = checked.behaviorBodies().get("pick");
        CoverageSites.Plan plan = checked.plan();
        ComparisonEmissionIndex copies = ComparisonEmissionIndex.ofBody(emitted, plan);

        Set<ModelOccurrence> written = new LinkedHashSet<>();
        statedIn(emitted, plan, written);
        ModelOccurrence twice = null;
        ModelOccurrence once = null;
        for (ModelOccurrence each : written) {
            switch (copies.madeFor(each).size()) {
                case 2 -> twice = each;
                case 1 -> once = each;
                default -> { }
            }
        }
        assertEquals(2, written.size(), () -> "two comparisons are written: " + written);
        List<ControlPlace.Outcome> outcomes = new ArrayList<>();
        for (ComparisonEmissionIndex.EmittedComparison each : copies.madeFor(twice)) {
            outcomes.add(plan.outcomeOf(each.occurrence(), true).orElseThrow());
        }
        ControlPlace.Outcome onlyOnce = plan.outcomeOf(
                copies.madeFor(once).getFirst().occurrence(), true).orElseThrow();
        PathReachability.Answers answers = compilation.db()
                .ask(new Adequacy.PathReached(module)).value().get("pick");
        return new Compiled(plan, copies, answers, twice, List.copyOf(outcomes), once, onlyOnce,
                emitted.pos());
    }

    /** Every comparison of the model the tree that runs evaluates, by what the model writes. */
    private static void statedIn(Core e, CoverageSites.Plan plan, Set<ModelOccurrence> out) {
        if (e instanceof Core.Binary binary) {
            plan.comparisons().occurrenceAt(binary)
                    .flatMap(ModelOccurrence::statedAt).ifPresent(out::add);
        }
        Core.forEachChild(e, child -> statedIn(child, plan, out));
    }

    /** The reading, with the reading of reach answering {@code set} at those places and as the
     *  compile did everywhere else. */
    private static NothingReaches with(Map<ControlPlace.Outcome, Reachability> set) {
        Map<ControlPlace, Reachability> found = new LinkedHashMap<>(COMPILED.answers().found());
        found.putAll(set);
        return new NothingReaches(Set.of(), COMPILED.copies(), COMPILED.plan(),
                new PathReachability.Answers(COMPILED.answers().numbering(), found,
                        COMPILED.answers().arriving()));
    }

    private static Reachability unreachable() {
        return new Reachability.Unreachable(Proof.conditionsThatCannotAllHold(List.of(
                PathDecision.ofACondition(COMPILED.where(), true))));
    }

    private static Reachability unsettled() {
        return new Reachability.Unsettled(WhyUnsettled.noWitness());
    }

    private static ShownBy at(ModelOccurrence comparison) {
        return new ShownBy.AtAnOutcome(comparison, true);
    }

    /** A way of one step, seen at {@code places} in that order. */
    private static DecisionReading.Ruled seenAt(ShownBy... places) {
        return new DecisionReading.Ruled(new DecisionRule(Map.of()),
                List.of(new RuleStep(List.of(places), List.of(), AnswersDemanded.NOTHING,
                        SaidOnTheWay.NONE)), true);
    }
}
