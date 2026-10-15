package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.check.PathReachability;
import souther.compiler.core.Core;
import souther.compiler.coverage.ComparisonEmissionIndex;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.SourcePos;
import souther.compiler.partition.AnswersDemanded;
import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.RuleStep;
import souther.compiler.partition.SaidOnTheWay;
import souther.compiler.partition.ShownBy;
import souther.compiler.coverage.SeenConditionOutcome;
import souther.compiler.query.Adequacy.DecisionSearch.NothingReaches;
import souther.compiler.reach.ComparisonArrival;
import souther.compiler.reach.PathDecision;
import souther.compiler.reach.Proof;
import souther.compiler.reach.Reachability;
import souther.compiler.reach.WhyUnsettled;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

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

    /**
     * A row seen bringing one copy out the way both were proven not to come out takes back that
     * copy's proof and no other, and says which it took back.
     */
    @Test
    void aRowAtOneCopyTakesBackThatCopysProofAlone() {
        ControlPlace.Outcome first = COMPILED.twice().get(0);
        ControlPlace.Outcome second = COMPILED.twice().get(1);
        PathReachability.Answers.AsRun run = proven(Map.of(
                first, unreachable(), second, unreachable()), Map.of())
                .asRunWith(Set.of(), Set.of(seen(first)));

        assertEquals(Set.of(first), run.contradicted().places(),
                "the copy a row came out of is the proof shown wrong");
        assertInstanceOf(Reachability.Reachable.class, run.answers().at(first));
        assertInstanceOf(Reachability.Unreachable.class, run.answers().at(second),
                "and the other copy's proof stands: a row at one call is nothing about another");
    }

    /**
     * A rule that only the proof taken back left no row is in, and says which proof that was —
     * which is why it is asked at all.
     */
    @Test
    void aRuleOnlyTheTakenBackProofLeftOutIsInAndNamesIt() {
        ControlPlace.Outcome first = COMPILED.twice().get(0);
        NothingReaches reading = reading(proven(Map.of(
                first, unreachable(), COMPILED.twice().get(1), unreachable()), Map.of())
                .asRunWith(Set.of(), Set.of(seen(first))));
        DecisionReading.Ruled way = seenAt(at(COMPILED.writtenTwice()));

        assertNull(reading.onTheWay(way), "a proof a row went against excludes nothing");
        assertEquals(Set.of(first), reading.shownWrongOnTheWay(way),
                "and the rule names the proof that would have");
    }

    /**
     * A rule another proof leaves no row stays out, by that proof: taking back one proof on its
     * way does not take back the others. And a place still out is refused the proofs taken back,
     * since what excludes it is something that stands.
     */
    @Test
    void aRuleAnotherProofLeavesOutStaysOutByIt() {
        ControlPlace.Outcome first = COMPILED.twice().get(0);
        NothingReaches reading = reading(proven(Map.of(
                first, unreachable(), COMPILED.twice().get(1), unreachable(),
                COMPILED.once(), unreachable()), Map.of())
                .asRunWith(Set.of(), Set.of(seen(first))));
        DecisionReading.Ruled way = seenAt(at(COMPILED.writtenTwice()), at(COMPILED.writtenOnce()));

        RuleRequirement.Excluded out = reading.onTheWay(way);
        assertEquals(new RuleRequirement.Excluded.AComparisonOutcomeNothingReaches(
                COMPILED.writtenOnce(), true), out, "the fork's own comparison is still proven");
        assertThrows(IllegalArgumentException.class,
                () -> new SettledAt(way, RuleSettlement.read(out), Set.of(first)),
                "a place excluded by a proof that stands rests on no proof taken back");
    }

    /**
     * What a place of a rule is settled with: a place left open names the proof taken back on its
     * way, and a place still excluded names none, whatever its way passed.
     */
    @Test
    void aPlaceIsSettledWithTheProofsItNoLongerRestsOn() {
        ControlPlace.Outcome first = COMPILED.twice().get(0);
        NothingReaches reading = reading(proven(Map.of(
                first, unreachable(), COMPILED.twice().get(1), unreachable()), Map.of())
                .asRunWith(Set.of(), Set.of(seen(first))));
        DecisionReading.Ruled way = seenAt(at(COMPILED.writtenTwice()));

        assertEquals(Set.of(first), Adequacy.DecisionSearch.settledAt(way,
                        RuleSettlement.of(new RuleRequirement.Unsettled.AComposedRowWentElsewhere(),
                                CompositionAccount.NOTHING), reading).shownWrong(),
                "a place now searched names what would have left it out");
        assertEquals(Set.of(), Adequacy.DecisionSearch.settledAt(way,
                        RuleSettlement.read(new RuleRequirement.Excluded
                                .AComparisonOutcomeNothingReaches(COMPILED.writtenOnce(), true)),
                        reading).shownWrong(),
                "and a place excluded by something that stands names nothing");
    }

    /** The controls: no row, and a row at a place nothing was proven of, take nothing back. */
    @Test
    void aRowWhereNothingWasProvenTakesNothingBack() {
        ControlPlace.Outcome once = COMPILED.once();
        PathReachability.Answers proven = proven(Map.of(
                COMPILED.twice().get(0), unreachable(), COMPILED.twice().get(1), unreachable(),
                once, unsettled()), Map.of());

        assertEquals(PathReachability.Answers.Contradictions.NONE,
                proven.asRunWith(Set.of(), Set.of()).contradicted(), "no row ran");
        PathReachability.Answers.AsRun ran = proven.asRunWith(Set.of(), Set.of(seen(once)));
        assertEquals(PathReachability.Answers.Contradictions.NONE, ran.contradicted(),
                "nothing was proven where the row went");
        assertInstanceOf(Reachability.Reachable.class, ran.answers().at(once),
                "and the row is a witness there all the same");
        assertEquals(Set.of(), reading(ran).shownWrongOnTheWay(
                seenAt(at(COMPILED.writtenTwice()))), "so a rule names no proof");
    }

    /**
     * A row at a comparison arrived at it, so a proof that nothing arrives there is taken back —
     * at that copy, as what restricts nothing, and kept apart from its ways' proofs.
     */
    @Test
    void aRowAtACopyTakesBackThatNothingArrivesThere() {
        ControlPlace.Outcome first = COMPILED.twice().get(0);
        ControlPlace.Outcome second = COMPILED.twice().get(1);
        PathReachability.Answers.AsRun run = proven(Map.of(first, unsettled()),
                Map.of(first.occurrence(), new ComparisonArrival.NothingArrives(),
                        second.occurrence(), new ComparisonArrival.NothingArrives()))
                .asRunWith(Set.of(), Set.of(seen(first)));

        assertEquals(Set.of(first.occurrence()), run.contradicted().emptyArrivals(),
                "the copy a row came to is the arrival shown wrong");
        assertEquals(Set.of(), run.contradicted().places(),
                "and that way of it was never proven, so no place is");
        assertInstanceOf(ComparisonArrival.NoProjection.class,
                run.answers().arrivals().arrivalAt(first.occurrence()),
                "what arrives restricts nothing");
        assertInstanceOf(ComparisonArrival.NothingArrives.class,
                run.answers().arrivals().arrivalAt(second.occurrence()),
                "and the other copy's proof stands");
    }

    /**
     * The same of an arm: a row through an arm proven shut takes the rule through it back in, and
     * the rule names the arm — where, with no row, the arm is what leaves it no row.
     */
    @Test
    void anArmOnlyTheTakenBackProofLeftOutIsInAndNamesIt() {
        CoverageSites.ArmSite high = COMPILED.arms().getFirst();
        PathReachability.Answers proven = proven(Map.of(high.place(), unreachable()), Map.of());
        DecisionReading.Ruled way = seenAt(new ShownBy.AtAnArm(
                ModelOccurrence.statedAt(high.place().arm().fork()).orElseThrow(
                        () -> new AssertionError("the arm is one the model writes: " + high)),
                high.place().arm().part()));

        NothingReaches unrun = NothingReaches.of(COMPILED.arms(), COMPILED.copies(),
                COMPILED.plan(), proven.asRunWith(Set.of(), Set.of()));
        assertEquals(new RuleRequirement.Excluded.AnArmNothingReaches(
                high.obligation().asWritten()), unrun.onTheWay(way), "no row, and the arm is shut");

        NothingReaches ran = NothingReaches.of(COMPILED.arms(), COMPILED.copies(),
                COMPILED.plan(), proven.asRunWith(Set.of(high.index()), Set.of()));
        assertNull(ran.onTheWay(way), "a row went through it");
        assertEquals(Set.of(high.place()), ran.shownWrongOnTheWay(way),
                "and the rule names the proof that would have left it no row");
    }

    /**
     * What a body is divided by is the same whichever arms and ways the rows went through, where
     * no row came to a construct proven to be arrived at by nothing — so a run that goes
     * somewhere new divides nothing again. The places themselves do move: a row is a witness.
     */
    @Test
    void whatArrivesAtTheComparisonsMovesOnlyWhereAnArrivalIsTakenBack() {
        CoverageSites.ArmSite high = COMPILED.arms().getFirst();
        ControlPlace.Outcome first = COMPILED.twice().get(0);
        PathReachability.Answers proven = proven(Map.of(), Map.of());
        PathReachability.Answers.AsRun none = proven.asRunWith(Set.of(), Set.of());
        PathReachability.Answers.AsRun somewhere = proven.asRunWith(Set.of(high.index()),
                Set.of(seen(first)));

        assertNotEquals(none.answers(), somewhere.answers(), "the rows went somewhere");
        assertEquals(none.answers().arrivals(), somewhere.answers().arrivals(),
                "and what arrives at the constructs lines are drawn at is what it was");
    }

    // --- what the compile made, and answers put over it --------------------------------------------

    /**
     * The plan and the copies, and the reading of reach the compile made.
     *
     * @param writtenTwice the key's comparison, as the model writes it
     * @param twice        where each of its two copies comes out true
     * @param writtenOnce  the fork's own comparison
     * @param once         where its one copy comes out true
     * @param arms         the arms of the fork the model writes, in the order the plan holds
     *                     them — and not the library's own, which the model states nothing of
     * @param where        somewhere in the body, for a proof set by hand to name
     */
    private record Compiled(CoverageSites.Plan plan, ComparisonEmissionIndex copies,
                            PathReachability.Answers answers,
                            ModelOccurrence writtenTwice, List<ControlPlace.Outcome> twice,
                            ModelOccurrence writtenOnce, ControlPlace.Outcome once,
                            List<CoverageSites.ArmSite> arms, SourcePos where) {}

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
                plan.arms("pick").stream().filter(site ->
                        ModelOccurrence.statedAt(site.place().arm().fork()).isPresent()).toList(),
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
     *  compile did everywhere else, and no row run. */
    private static NothingReaches with(Map<ControlPlace.Outcome, Reachability> set) {
        return reading(new PathReachability.Answers.AsRun(proven(set, Map.of()),
                PathReachability.Answers.Contradictions.NONE));
    }

    /** What the rule's reader makes of {@code run}. */
    private static NothingReaches reading(PathReachability.Answers.AsRun run) {
        return NothingReaches.of(List.of(), COMPILED.copies(), COMPILED.plan(), run);
    }

    /** The reading of reach answering {@code set} and {@code arriving} at those places and as the
     *  compile did everywhere else, before any row ran. */
    private static PathReachability.Answers proven(Map<? extends ControlPlace, Reachability> set,
                                                   Map<ConstructOccurrence, ComparisonArrival>
                                                           arriving) {
        Map<ControlPlace, Reachability> found = new LinkedHashMap<>(COMPILED.answers().found());
        found.putAll(set);
        PathReachability.Arrivals compiled = COMPILED.answers().arrivals();
        Map<ConstructOccurrence, ComparisonArrival> arrivals =
                new LinkedHashMap<>(compiled.arriving());
        arrivals.putAll(arriving);
        return new PathReachability.Answers(COMPILED.answers().numbering(), found,
                new PathReachability.Arrivals(compiled.numbering(), arrivals,
                        compiled.recordedAt()));
    }

    /** A row seen bringing the comparison out the way {@code place} is. */
    private static SeenConditionOutcome seen(ControlPlace.Outcome place) {
        return new SeenConditionOutcome(place.at(), place.held());
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
