package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSites;
import souther.compiler.abort.GetsPast;
import souther.compiler.check.ARowsRun;
import souther.compiler.check.ClausesInOrder;
import souther.compiler.check.StopOrigin;
import souther.compiler.check.ValueTemplates;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.inputs.ABoundThatKeepsEveryRunGoing;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.EveryRunStops;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatKeepsEveryRunGoing;
import souther.compiler.inputs.WhyAStopIsNotShown;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Whether a run of a behavior stops at each step it may stop at: shown not to, shown to, or
 * neither — the one place that says it, of every step the walk of the body met
 * ({@link WhereARunMayStop}), whether or not a comparison comes after it.
 *
 * <p>Each step is judged where it stands, along the way to it and over what a run works out
 * before it, and never along the way to something after it: a condition a run asks after the
 * step is not one a run stopping there got to. A step met on several ways, or met where the
 * walk reads it on each application of a function value, is judged on each and put together
 * ({@link ConstructionStopAssessment#together}): a stop shown on one is a run that stops; no
 * stop only where every way is read and shows none.
 *
 * <p>That no run stops rests on what a way leaves of the input, which holds every run getting
 * there and more ({@link WhatAWayLeavesOfAValue}); that one does rests on one value of the input
 * that is on the way, gets past everything worked out before the step, and stops there
 * ({@link StopAssessment#aStopLookedFor}, {@link ConstructionStopAssessment#ofASite}). A
 * construction is asked what its type asks; anything else, what its operator does.
 */
final class StopsOfABody {

    /**
     * What is shown of one step.
     *
     * @param step          the node
     * @param operations    what is shown of each operation it works out, where it is no
     *                      construction
     * @param construction  what is shown of it, where it is a construction
     * @param everyRunStops the rows at which every run getting to it stops there, by a way on
     *                      which what comes first is read; none where none is known. Said of the
     *                      runs that get to the step, and not of every run of the behavior: the
     *                      way there is what decides whether a row gets there
     * @param keeping       the declarations that keep every run getting to it from taking a
     *                      number past its type there ({@link WhatKeepsEveryRunGoing}); none where
     *                      no such region is said
     */
    record AtAStep(Core step, List<StopAssessment.Judgement> operations,
                   Optional<ConstructionStopAssessment.Judgement> construction,
                   List<EveryRunStops> everyRunStops, Optional<WhatKeepsEveryRunGoing> keeping) {

        AtAStep {
            operations = List.copyOf(operations);
            everyRunStops = List.copyOf(everyRunStops);
        }
    }

    private final WhereARunMayStop where;
    private final WhatConditionsState conditions;
    private final InputReading read;
    private final ValueTemplates definitions;
    private List<AtAStep> judged;

    StopsOfABody(WhereARunMayStop where, WhatConditionsState conditions, InputReading read,
                 ValueTemplates definitions) {
        this.where = where;
        this.conditions = conditions;
        this.read = read;
        this.definitions = definitions;
    }

    /**
     * What is shown of every step, in the order the walk first met each. Worked out once.
     *
     * <p>Not of a step a run of a row is taken to get past ({@link ARowsRun#completionOf}): an
     * {@code unreachable}, which states that no run reaches it; a call of a behavior whose own rows
     * answer for its body; and an operation that ends a run only past what a representation
     * holds, which is said once of the operation. What is said of those is said where their owner
     * says it, and nothing here says it again.
     */
    synchronized List<AtAStep> judged() {
        if (judged == null) {
            List<AtAStep> out = new ArrayList<>();
            for (Core step : where.steps()) {
                if (gotPast(step)) {
                    continue;
                }
                out.add(Core.withoutStanding(step) instanceof Core.Construct made
                        ? new AtAStep(step, List.of(), Optional.of(ofAConstruction(made)),
                                List.of(), Optional.empty())
                        : new AtAStep(step, ofAnOperation(step, List.of()), Optional.empty(),
                                everyRunStops(step), keeping(step)));
            }
            judged = List.copyOf(out);
            judged.forEach(each -> byStep.put(each.step(), each));
        }
        return judged;
    }

    /**
     * Whether a run may stop at {@code step}: it is shown to, or it is not shown not to. A node
     * the walk did not meet as a step of this body is one nothing here shows a run gets past.
     * What a reader of the rows that get past a step asks, which is a question of what this says
     * and not one it answers again.
     */
    synchronized boolean mayStopAt(Core step) {
        judged();
        AtAStep each = byStep.get(Core.withoutStanding(step));
        if (each == null) {
            return !gotPast(step);
        }
        return each.construction().map(made -> !(made
                        instanceof ConstructionStopAssessment.Judgement.Safe)).orElse(false)
                || each.operations().stream().anyMatch(one ->
                        !(one instanceof StopAssessment.Judgement.Safe));
    }

    /** What is shown of each step, by the node it is, once {@link #judged} is worked out. */
    private final Map<Core, AtAStep> byStep = new IdentityHashMap<>();

    /** Whether a run of a row is taken to get past {@code step} whatever the input holds
     *  ({@link ARowsRun#completionOf}). */
    private boolean gotPast(Core step) {
        return ARowsRun.completionOf(step, read.rules().declarations().answers())
                instanceof GetsPast.Always;
    }

    /**
     * Each way a run gets to a step, with where the walk met it on that way, and the names as they
     * stand there on it: inside a closure handed values written out, on one application of it.
     *
     * @param onTheWay whether every run taking the way makes the application, so that the way
     *                 holds every condition a run getting there meets; a value looked for on a way
     *                 that does not is not shown to get there
     */
    private record Reached(WhereARunMayStop.Met met, WaysToASite.Reach reach, InputReads reads,
                           boolean onTheWay) {}

    /** Every way a run gets to {@code step}, and whether they are every way there is. */
    private record Ways(List<Reached> each, boolean every) {}

    /**
     * Every way a run gets to {@code step}: by each way into the tree it stands in, and inside a
     * closure handed values written out, on each application a run makes on some row. Inside one
     * handed none, on none.
     */
    private Ways waysTo(Core step) {
        List<Reached> each = new ArrayList<>();
        boolean every = true;
        for (WhereARunMayStop.Met met : where.everyPlace(step)) {
            WaysToASite ways = met.ways().get();
            every &= ways.every();
            for (WaysToASite.Reach reach : ways.each()) {
                switch (met.applying()) {
                    case ClosureApplications.None _ -> { }
                    case ClosureApplications.Each(var made) -> made.stream()
                            .filter(ClosureApplications.Application::isMadeOnSomeRow)
                            .forEach(one -> each.add(new Reached(met, reach, one.reads(),
                                    ClosureApplications.madeWhateverTheRow(one))));
                    default -> each.add(new Reached(met, reach, met.reads(), true));
                }
            }
        }
        return new Ways(each, every);
    }

    // ---- constructions ----

    private ConstructionStopAssessment.Judgement ofAConstruction(Core.Construct made) {
        Ways ways = waysTo(made);
        List<AConstructionOnTheWay.Reach> reaches = new ArrayList<>();
        List<SearchRegion> regions = new ArrayList<>();
        for (int at = 0; at < ways.each().size(); at++) {
            WaysToASite.Reach reach = ways.each().get(at).reach();
            reaches.add(new AConstructionOnTheWay.Reach(at, reach.way(), reach.way(),
                    reach.before(), reach.read()));
            if (Reachability.of(new WayToTheBorder(reach.way()), read.quantities().region())
                    instanceof Reachability.Reaching reaching) {
                regions.add(reaching.region());
            }
        }
        AConstructionOnTheWay one = new AConstructionOnTheWay(made, asked(made), reaches,
                ways.every());
        return ConstructionStopAssessment.ofASite(one, regions, asks(), constructionWays(), read,
                definitions);
    }

    /** What {@code made} asks, read with the names as they stand where the walk met it. */
    private AConstructionOnTheWay.Asked asked(Core.Construct made) {
        if (ClausesInOrder.at(made, read.rules()).governsNothing()) {
            return new AConstructionOnTheWay.Asked.Nothing();
        }
        Optional<WhereARunMayStop.Met> met = where.at(made);
        if (met.isEmpty()) {
            return new AConstructionOnTheWay.Asked.NotRead();
        }
        return conditions.whereItsOperatorsAnswer(made, met.get().reads(), read).asks().stream()
                .filter(ask -> ask.of(made)).findFirst()
                .<AConstructionOnTheWay.Asked>map(AConstructionOnTheWay.Asked.Read::new)
                .orElseGet(AConstructionOnTheWay.Asked.NotRead::new);
    }

    private List<ConstructionAsk> asks;

    /** What every construction the walk met on one way asks, as a run getting past it meets. */
    private List<ConstructionAsk> asks() {
        if (asks == null) {
            List<ConstructionAsk> out = new ArrayList<>();
            for (Core step : where.steps()) {
                if (Core.withoutStanding(step) instanceof Core.Construct made
                        && asked(made) instanceof AConstructionOnTheWay.Asked.Read(var ask)) {
                    out.add(ask);
                }
            }
            asks = List.copyOf(out);
        }
        return asks;
    }

    /** The way the walk met each construction on, where it met it once. */
    private Map<Core, List<OnTheWay>> constructionWays() {
        Map<Core, List<OnTheWay>> out = new IdentityHashMap<>();
        for (Core step : where.steps()) {
            if (Core.withoutStanding(step) instanceof Core.Construct) {
                where.at(step).ifPresent(met -> out.put(step, met.way()));
            }
        }
        return out;
    }

    // ---- operations ----

    /**
     * What is shown of each operation {@code step} works out: on every way a run gets to it, the
     * operation as the names stand there, put together over the ways. A value looked for meets
     * {@code within} as it meets the way: what a region of the input is asked of where it is to
     * be said as far out as it can go.
     */
    private List<StopAssessment.Judgement> ofAnOperation(Core step,
                                                         List<TakenConstraint.Affine> within) {
        Ways ways = waysTo(step);
        List<List<StopAssessment.Judgement>> byWay = new ArrayList<>();
        for (Reached each : ways.each()) {
            byWay.add(onAWay(step, each, within));
        }
        return together(byWay, ways.every());
    }

    /**
     * The rows at which every run getting to {@code step} by some way stops there: where its own
     * operation is past its type and everything worked out before it on that way is within its
     * own ({@link UndividedByARelation#everyRunStopsIn}). Asked of a way only where what comes
     * first on it is read.
     */
    private List<EveryRunStops> everyRunStops(Core step) {
        Set<EveryRunStops> out = new LinkedHashSet<>();
        for (Reached each : waysTo(step).each()) {
            WhatAWayLeavesOfAValue left = WhatAWayLeavesOfAValue.along(read, each.reach().way());
            if (left == null || !each.onTheWay() || !each.reach().read().get()
                    || !(Reachability.of(new WayToTheBorder(each.reach().way()),
                            read.quantities().region()) instanceof Reachability.Reaching reaching)) {
                continue;
            }
            GotPast gotPast = each.reach().before().get()
                    .map(first -> gotPast(first.onSomeRun(), left)).orElse(null);
            List<StopAssessment.Site> sites = sitesOf(step, each);
            if (gotPast == null || sites == null) {
                continue;
            }
            Set<String> own = new HashSet<>();
            sites.forEach(site -> own.add(site.written()));
            StopEvidence evidence = AffineReading.stopsOfEvaluating(Core.withoutStanding(step),
                    each.reads(), read, AffineReading.WhatTheAnalysisAnswersFor.NOTHING);
            for (EveryRunStops stops : evidence.everyRunStopsIn(read, List.of(reaching.region()),
                    gotPast.operations(), EvaluationPlaces.none())) {
                if (own.contains(stops.operation())) {
                    out.add(stops);
                }
            }
        }
        return List.copyOf(out);
    }

    /**
     * The declarations that keep every run getting to {@code step} from taking a number past its
     * type in what it works out ({@link UndividedByARelation#boundsThatKeepEveryRunGoing}), with
     * each bound said as far out as it can be where a run with it declared one step further out,
     * every other declaration holding, is shown to stop there: a claim about the region, asked
     * once it is whole.
     */
    private Optional<WhatKeepsEveryRunGoing> keeping(Core step) {
        List<StopEvidence> worked = new ArrayList<>();
        for (Reached each : waysTo(step).each()) {
            worked.add(AffineReading.stopsOfEvaluating(Core.withoutStanding(step), each.reads(),
                    read, AffineReading.WhatTheAnalysisAnswersFor.NOTHING));
        }
        return UndividedByARelation.boundsThatKeepEveryRunGoing(worked, read).map(region -> {
            Set<ABoundThatKeepsEveryRunGoing> farOut = new LinkedHashSet<>();
            for (ABoundThatKeepsEveryRunGoing bound : region.bounds()) {
                List<TakenConstraint.Affine> within = new ArrayList<>();
                for (ABoundThatKeepsEveryRunGoing other : region.bounds()) {
                    BigInteger at = other != bound ? other.at() : other.atMost()
                            ? other.at().add(BigInteger.ONE)
                            : other.at().subtract(BigInteger.ONE);
                    for (TermPath place : UndividedByARelation.placesHeldBy(other.holder(),
                            read)) {
                        within.add(new TakenConstraint.Affine(new LinearForm<>(
                                ExactRatio.of(at).negated(),
                                Map.of(new NumericTerm.ValueOf(place), ExactRatio.ONE)),
                                other.atMost() ? Rel.LE : Rel.GE));
                    }
                }
                if (ofAnOperation(step, within).stream()
                        .anyMatch(StopAssessment.Judgement.Stops.class::isInstance)) {
                    farOut.add(bound);
                }
            }
            return region.asFarOutAsCanBe(farOut);
        });
    }

    /** What is shown of {@code step}'s operations by one way a run gets to it. */
    private List<StopAssessment.Judgement> onAWay(Core step, Reached reached,
                                                  List<TakenConstraint.Affine> within) {
        WhatAWayLeavesOfAValue left = WhatAWayLeavesOfAValue.along(read, reached.reach().way());
        if (left == null) {
            return List.of(new StopAssessment.Judgement.Safe(null,
                    StopAssessment.WhyNone.NOT_WORKED_OUT));
        }
        Denotation here = new Denotation(step, reached.reads());
        if (left.endsNoRunAt(here)) {
            return List.of(new StopAssessment.Judgement.Safe(null,
                    StopAssessment.WhyNone.WITHIN_ITS_ENDS));
        }
        List<StopAssessment.Site> sites = sitesOf(step, reached);
        if (sites == null) {
            return List.of(new StopAssessment.Judgement.Unresolved(null,
                    WhyAStopIsNotShown.NO_OPERATION_TOLD, Optional.of(StopOrigin.of(step,
                            read.rules().declarations().answers()))));
        }
        List<StopAssessment.Judgement> out = new ArrayList<>();
        for (StopAssessment.Site site : sites) {
            out.add(judgedOn(site, reached, left, within));
        }
        return out;
    }

    /**
     * What a run may stop at in {@code step} itself, with the names as {@code reached} has them:
     * each operation of whole numbers it is, past its ends, and a quotient with its divisor at
     * nought. Null where it is neither, or what it is over is not read.
     */
    private List<StopAssessment.Site> sitesOf(Core step, Reached reached) {
        Core node = Core.withoutStanding(step);
        List<StopAssessment.Site> out = new ArrayList<>();
        StopEvidence evidence = AffineReading.stopsOfEvaluating(node, reached.reads(), read,
                AffineReading.WhatTheAnalysisAnswersFor.NOTHING);
        for (UndividedByARelation.IntOperation operation
                : evidence.operations().operations()) {
            if (operation.origin().node() != null
                    && Core.withoutStanding(operation.origin().node()) == node) {
                out.add(new StopAssessment.Site.PastItsEnds(operation));
            }
        }
        if (node instanceof Core.Binary quotient
                && AbortSites.ofAnOperator(quotient).contains(AbortKind.DIVISION_BY_ZERO)) {
            LinearForm<NumericTerm> divisor = AffineReading.formOf(quotient.right(),
                    reached.reads(), read, new ElementsMet(),
                    AffineReading.Unkept.EVERY_NAME_AFRESH);
            if (divisor == null) {
                return null;
            }
            out.add(new StopAssessment.Site.ByNought(divisor));
        }
        return out.isEmpty() ? null : out;
    }

    /** What is shown of {@code site} by one way: none where every value the way leaves keeps it
     *  in, and otherwise a value looked for past what is worked out before it, meeting
     *  {@code within} as well. */
    private StopAssessment.Judgement judgedOn(StopAssessment.Site site, Reached reached,
                                              WhatAWayLeavesOfAValue left,
                                              List<TakenConstraint.Affine> within) {
        switch (site) {
            case StopAssessment.Site.PastItsEnds(var operation) -> {
                if (left.keepsWithinItsEnds(operation)) {
                    return new StopAssessment.Judgement.Safe(site,
                            StopAssessment.WhyNone.WITHIN_ITS_ENDS);
                }
            }
            case StopAssessment.Site.ByNought(var divisor) -> {
                if (left.keepsAwayFromNought(divisor)) {
                    return new StopAssessment.Judgement.Safe(site,
                            StopAssessment.WhyNone.DIVISOR_AWAY_FROM_NOUGHT);
                }
            }
        }
        if (!reached.onTheWay() || !reached.reach().read().get()) {
            return new StopAssessment.Judgement.Unresolved(site,
                    WhyAStopIsNotShown.A_CONDITION_NOT_READ);
        }
        Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction> before =
                reached.reach().before().get();
        List<TakenConstraint.Affine> way = StopAssessment.asRelations(reached.reach().way());
        if (way == null) {
            return new StopAssessment.Judgement.Unresolved(site,
                    WhyAStopIsNotShown.A_CONDITION_NOT_READ);
        }
        way.addAll(within);
        GotPast gotPast = before.map(first -> gotPast(first.onSomeRun(), left)).orElse(null);
        if (gotPast == null) {
            return new StopAssessment.Judgement.Unresolved(site,
                    WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        }
        return StopAssessment.aStopLookedFor(site, gotPast.operations(), gotPast.divisors(), left,
                way, read);
    }

    /** What a value has to get past before a step: each operation within its ends, and each
     *  divisor away from nought, a divisor no form of the input's numbers among them as null. */
    private record GotPast(List<UndividedByARelation.IntOperation> operations,
                           List<LinearForm<NumericTerm>> divisors) {}

    /**
     * What a run works out first in {@code parts} asks of a value that gets past it, every step in
     * them that may end a run read as it stands where the walk met it; null where one is not read,
     * or is a step a value is not asked of here. A step every value {@code left} leaves gets past
     * ({@link WhatAWayLeavesOfAValue#endsNoRunAt}) asks nothing.
     */
    private GotPast gotPast(List<Core> parts, WhatAWayLeavesOfAValue left) {
        List<UndividedByARelation.IntOperation> operations = new ArrayList<>();
        List<LinearForm<NumericTerm>> divisors = new ArrayList<>();
        Set<Core> through = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Core part : parts) {
            if (!past(part, left, operations, divisors, through)) {
                return null;
            }
        }
        return new GotPast(operations, divisors);
    }

    private boolean past(Core e, WhatAWayLeavesOfAValue left,
                         List<UndividedByARelation.IntOperation> operations,
                         List<LinearForm<NumericTerm>> divisors, Set<Core> through) {
        Core node = Core.withoutStanding(e);
        if (Evaluated.makesAFunction(node)) {
            return true;
        }
        Core template = definitions.builtBy(node);
        if (template != null) {
            if (!through.add(template)) {
                return false;
            }
            boolean past = past(template, left, operations, divisors, through);
            through.remove(template);
            return past;
        }
        if (node instanceof Core.IfConstructed attempt) {
            boolean[] all = {true};
            WhatARunMayEndFor.forEachWorkedOut(attempt, (part, _) -> all[0] = all[0]
                    && past(part, left, operations, divisors, through));
            return all[0];
        }
        if (WhereARunMayStop.aStepARunMayStopAt(node) && !aStepGotPast(node, left, operations,
                divisors)) {
            return false;
        }
        boolean[] all = {true};
        Core.forEachChild(node, child -> all[0] = all[0]
                && past(child, left, operations, divisors, through));
        return all[0];
    }

    /** What {@code step}, met where the walk met it once, asks of a value that gets past it, into
     *  {@code operations} and {@code divisors}; false where that is not read. */
    private boolean aStepGotPast(Core step, WhatAWayLeavesOfAValue left,
                                 List<UndividedByARelation.IntOperation> operations,
                                 List<LinearForm<NumericTerm>> divisors) {
        if (gotPast(step)) {
            return true;
        }
        Optional<WhereARunMayStop.Met> met = where.at(step);
        if (met.isEmpty()) {
            return false;
        }
        if (left.endsNoRunAt(new Denotation(step, met.get().reads()))) {
            return true;
        }
        if (step instanceof Core.Construct) {
            return false;
        }
        List<StopAssessment.Site> sites = sitesOf(step,
                new Reached(met.get(), null, met.get().reads(), true));
        if (sites == null) {
            return false;
        }
        for (StopAssessment.Site site : sites) {
            switch (site) {
                case StopAssessment.Site.PastItsEnds(var operation) -> operations.add(operation);
                case StopAssessment.Site.ByNought(var divisor) -> divisors.add(divisor);
            }
        }
        return true;
    }

    /**
     * What every way shows, put together operation by operation as {@link #ofAnOperation} says:
     * a stop shown by one way, whatever the others come to; otherwise the first not resolved;
     * otherwise none, where the ways are every way, and not resolved where they are not.
     */
    private static List<StopAssessment.Judgement> together(
            List<List<StopAssessment.Judgement>> byWay, boolean every) {
        List<StopAssessment.Judgement> all = new ArrayList<>();
        byWay.forEach(all::addAll);
        for (StopAssessment.Judgement each : all) {
            if (each instanceof StopAssessment.Judgement.Stops) {
                return List.of(each);
            }
        }
        for (StopAssessment.Judgement each : all) {
            if (each instanceof StopAssessment.Judgement.Unresolved) {
                return List.of(each);
            }
        }
        if (!every) {
            return List.of(new StopAssessment.Judgement.Unresolved(null,
                    WhyAStopIsNotShown.REACH_NOT_SHOWN));
        }
        return all.isEmpty() ? List.of(new StopAssessment.Judgement.Safe(null,
                StopAssessment.WhyNone.NOT_WORKED_OUT)) : List.of(all.getFirst());
    }
}
