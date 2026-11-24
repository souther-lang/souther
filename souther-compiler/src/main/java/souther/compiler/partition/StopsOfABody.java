package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSites;
import souther.compiler.abort.GetsPast;
import souther.compiler.check.ARowsRun;
import souther.compiler.check.Choice;
import souther.compiler.check.ClausesInOrder;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.Shape;
import souther.compiler.check.StopOrigin;
import souther.compiler.check.TypeView;
import souther.compiler.check.ValueTemplates;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.inputs.ABoundThatKeepsEveryRunGoing;
import souther.compiler.inputs.AConstructionStopNotShown;
import souther.compiler.inputs.Denotation;
import souther.compiler.types.BindingId;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.EveryRunStops;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatAConstructionAsks;
import souther.compiler.inputs.WhatARelationLeavesUndivided;
import souther.compiler.inputs.WhatKeepsEveryRunGoing;
import souther.compiler.inputs.WhyAConstructionStopIsNotShown;
import souther.compiler.inputs.WhyAStopIsNotShown;
import souther.compiler.inputs.WrittenOutElements;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.BooleanSupplier;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * Whether a run of a behavior stops at each step it may stop at: shown not to, shown to, or
 * neither — the one place that says it, of every step the walk of the body met
 * ({@link WhereARunMayStop}), whether or not a comparison comes after it.
 *
 * <p>Each step is judged where it stands, along the way to it and over what a run works out
 * before it, and never along the way to something after it: a condition a run asks after the
 * step is not one a run stopping there got to. A step met on several ways, or met where the
 * walk reads it on each application of a function value, is judged on each and put together
 * ({@link WhatEveryWayShows#together}): a stop shown on one is a run that stops; no
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
        this.readsWith = Pullback.whatEveryReadingReadsWith(read);
        this.owner = WorkedOutToReachIt.of(read);
    }

    /**
     * What a run works out to reach a value, one for the body: every step asks it of what the
     * steps before it work out, and what it has worked out of a name is worked out once however
     * many steps after it ask.
     */
    private final WorkedOutToReachIt owner;

    /** What a step is read with: what every reading of the input reads with, and nothing a rule
     *  answers for, since no rule is read here
     *  ({@link Pullback#whatEveryReadingReadsWith}). */
    private final AffineReading.WhatTheAnalysisAnswersFor readsWith;

    /**
     * What is shown of every step, in the order the walk first met each. Worked out once.
     *
     * <p>Not of a step a run of a row is taken to get past by a premise
     * ({@link ARowsRun#takenAsGotPast}): an {@code unreachable}, which states that no run reaches
     * it, and a call of a behavior whose own rows answer for its body. What is said of those is
     * said where their owner says it, and nothing here says it again.
     */
    synchronized List<AtAStep> judged() {
        if (judged == null) {
            List<AtAStep> out = new ArrayList<>();
            for (Core step : where.steps()) {
                if (!gotPast(step)) {
                    out.add(stepJudged(step));
                }
            }
            Map<Core, WhatKeepsEveryRunGoing> kept = keptTogether(out);
            List<AtAStep> withWhatKeepsThem = new ArrayList<>();
            for (AtAStep each : out) {
                withWhatKeepsThem.add(new AtAStep(each.step(), each.operations(),
                        each.construction(), each.everyRunStops(),
                        Optional.ofNullable(kept.get(each.step()))));
            }
            judged = List.copyOf(withWhatKeepsThem);
            judged.forEach(each -> byStep.put(each.step(), each));
        }
        return judged;
    }

    /**
     * The declarations that keep every run from taking a number past its type at every step of
     * {@code steps} a run may stop at that some declaration on the input can keep it from: one
     * region of what each of them works out, on every way a run gets to it, all together
     * ({@link UndividedByARelation#boundsThatKeepEveryRunGoing}), so that declaring all of it
     * keeps every run going at every one of them; none where no value of the input holds it all,
     * where what one step asks would leave another no value or stop every run there. Each bound
     * is said once, at the step whose own working asks it of itself, the first where several do,
     * and at the last of them where none does alone; a step a looser bound of its own keeps is
     * kept by the tighter one, and nothing is said there.
     *
     * <p>How far out a bound goes is asked of the region: it is as far out as one can be where a
     * run with it declared one step further out, every other declaration holding, is shown to
     * stop at one of the steps.
     */
    private Map<Core, WhatKeepsEveryRunGoing> keptTogether(List<AtAStep> steps) {
        List<Core> stopping = new ArrayList<>();
        List<StopEvidence> worked = new ArrayList<>();
        Map<Core, Optional<WhatKeepsEveryRunGoing>> ownOf = new IdentityHashMap<>();
        for (AtAStep each : steps) {
            if (each.construction().isPresent() || each.operations().stream()
                    .allMatch(StopAssessment.Judgement.Safe.class::isInstance)) {
                continue;
            }
            // What keeps every run going is said of every step together, so a step whose ways are
            // not every way there is, or one of which is not read, leaves nothing to say.
            Ways ways = waysTo(each.step());
            if (!ways.every()) {
                return Map.of();
            }
            List<StopEvidence> ofTheStep = new ArrayList<>();
            for (Reached way : ways.each()) {
                StopEvidence own = ownWorking(each.step(), way);
                if (own == null) {
                    return Map.of();
                }
                ofTheStep.add(own);
            }
            if (ofTheStep.isEmpty()) {
                continue;
            }
            stopping.add(each.step());
            worked.addAll(ofTheStep);
            ownOf.put(each.step(),
                    UndividedByARelation.boundsThatKeepEveryRunGoing(ofTheStep, read));
        }
        Optional<WhatKeepsEveryRunGoing> region =
                UndividedByARelation.boundsThatKeepEveryRunGoing(worked, read)
                        .flatMap(WhatKeepsEveryRunGoing::said);
        if (stopping.isEmpty() || region.isEmpty() || region.get().bounds().isEmpty()) {
            return Map.of();
        }
        Set<ABoundThatKeepsEveryRunGoing> farOut = new LinkedHashSet<>();
        for (ABoundThatKeepsEveryRunGoing bound : region.get().bounds()) {
            List<TakenConstraint.Affine> within = oneStepFurtherOut(bound, region.get());
            if (stopping.stream().anyMatch(step -> ofAnOperation(step, within).stream()
                    .anyMatch(StopAssessment.Judgement.Stops.class::isInstance))) {
                farOut.add(bound);
            }
        }
        Map<Core, Set<ABoundThatKeepsEveryRunGoing>> saidAt = new IdentityHashMap<>();
        for (ABoundThatKeepsEveryRunGoing bound : region.get().bounds()) {
            Core at = stopping.stream().filter(step -> ownOf.get(step)
                            .map(own -> own.bounds().contains(bound)).orElse(false))
                    .findFirst().orElse(stopping.getLast());
            saidAt.computeIfAbsent(at, _ -> new LinkedHashSet<>()).add(bound);
        }
        Map<Core, WhatKeepsEveryRunGoing> out = new IdentityHashMap<>();
        saidAt.forEach((step, bounds) -> {
            Map<ABoundThatKeepsEveryRunGoing.Holder, ABoundThatKeepsEveryRunGoing.Held> held =
                    new LinkedHashMap<>();
            bounds.forEach(bound -> held.put(bound.holder(),
                    region.get().held().get(bound.holder())));
            Set<ABoundThatKeepsEveryRunGoing> furthest = new LinkedHashSet<>(bounds);
            furthest.retainAll(farOut);
            out.put(step, new WhatKeepsEveryRunGoing(bounds, held, furthest,
                    region.get().shownTogether()));
        });
        return out;
    }

    /** Every declaration of {@code region} holding, and {@code bound} one step further out, as
     *  relations of the places the declarations hold. */
    private List<TakenConstraint.Affine> oneStepFurtherOut(ABoundThatKeepsEveryRunGoing bound,
                                                           WhatKeepsEveryRunGoing region) {
        List<TakenConstraint.Affine> within = new ArrayList<>();
        for (ABoundThatKeepsEveryRunGoing other : region.bounds()) {
            BigInteger at = other != bound ? other.at() : other.atMost()
                    ? other.at().add(BigInteger.ONE)
                    : other.at().subtract(BigInteger.ONE);
            for (TermPath place : UndividedByARelation.placesHeldBy(other.holder(), read)) {
                within.add(new TakenConstraint.Affine(new LinearForm<>(
                        ExactRatio.of(at).negated(),
                        Map.of(new NumericTerm.ValueOf(place), ExactRatio.ONE)),
                        other.atMost() ? Rel.LE : Rel.GE));
            }
        }
        return within;
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

    /**
     * What is shown of {@code step}, apart from what keeps its runs going, worked out once
     * whoever asks first: the list of every step, or a step after it that a run gets to past an
     * application of a function value it stands in. Null while it is being worked out, which is
     * a step asked of on the way to itself.
     */
    private AtAStep stepJudged(Core step) {
        Optional<AtAStep> known = stepsJudged.get(step);
        if (known != null) {
            return known.orElse(null);
        }
        stepsJudged.put(step, Optional.empty());
        AtAStep made = Core.withoutStanding(step) instanceof Core.Construct construct
                ? new AtAStep(step, List.of(), Optional.of(ofAConstruction(construct)),
                        List.of(), Optional.empty())
                : new AtAStep(step, ofAnOperation(step, List.of()), Optional.empty(),
                        everyRunStops(step), Optional.empty());
        stepsJudged.put(step, Optional.of(made));
        return made;
    }

    /** What {@link #stepJudged} has worked out, by the step; empty while it is being worked
     *  out. */
    private final Map<Core, Optional<AtAStep>> stepsJudged = new IdentityHashMap<>();

    /** What is shown of each step, by the node it is, once {@link #judged} is worked out. */
    private final Map<Core, AtAStep> byStep = new IdentityHashMap<>();

    /** Whether a run of a row is taken to get past {@code step} by a premise it is written under
     *  ({@link ARowsRun#takenAsGotPast}). */
    private boolean gotPast(Core step) {
        return ARowsRun.takenAsGotPast(step, read.rules().declarations().answers());
    }

    /**
     * Each way a run gets to a step, with where the walk met it on that way, and the names as they
     * stand there on it: inside a closure handed values written out, on one application of it.
     *
     * @param onTheWay whether every run taking the way makes the application, so that the way
     *                 holds every condition a run getting there meets; a value looked for on a way
     *                 that does not is not shown to get there
     * @param before   what a run on one application works out before the step, each part with the
     *                 names it is worked out in, where the way's own account of it is not read and
     *                 this one is ({@link #onEachApplication}); null otherwise
     * @param made     what a run meets for the application to be made at all, beside the way,
     *                 where the step stands inside a closure: what is met inside the closure on
     *                 the way to the step goes there and not onto the way
     *                 ({@link ClosureApplications#saysWhatStandsInIt}); null outside one
     * @param forEvery whether the application stands for every element a container holds, so
     *                 that a value looked for at the element is a list of one, on which what the
     *                 application is made under is met by that element
     *                 ({@link #madeOnTheElementAs})
     */
    private record Reached(WhereARunMayStop.Met met, WaysToASite.Reach reach, InputReads reads,
                           boolean onTheWay, BeforeAStep before, Proposition made,
                           boolean forEvery) {}

    /** Whether the way {@code reached} is by is on the way the walk carried: inside a closure
     *  judged on each application ({@link Reached#made}), as far as the closure, the application
     *  being {@link Reached#onTheWay}'s to say. */
    private static boolean wayRead(Reached reached) {
        return reached.made() != null ? reached.reach().readUpToTheApplications().get()
                : reached.reach().read().get();
    }

    /**
     * Every way a run gets to {@code step}, and whether they are every way there is.
     *
     * <p>What is said of a step beyond whether a run may stop there — the rows every run
     * getting there stops at, what keeps every run going — is a claim about every run that gets
     * there, and is made only of the ways that are every way there is. A claim one way holds is
     * proved under that way's conditions and in its names, and is said without them, so it is
     * made only where that way is the one way there is ({@link #areOne}).
     */
    private record Ways(List<Reached> each, boolean every) {

        /** Whether every run getting to the step gets there by one way, which is read. */
        boolean areOne() {
            return every && each.size() == 1;
        }
    }

    /**
     * Every way a run gets to {@code step}: by each way into the tree it stands in, and inside a
     * closure handed values written out, on each application a run makes on some row
     * ({@link #onEachApplication}). Inside one handed none, on none.
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
                    case ClosureApplications.Each(var made) ->
                            each.addAll(onEachApplication(step, met, reach, made));
                    default -> each.add(new Reached(met, reach, met.reads(), true, null, null,
                            false));
                }
            }
        }
        return new Ways(each, every);
    }

    /**
     * Whether {@code step} stands inside one closure, met once, that the owner of what a run works
     * out shows to end no run where the call it is handed to applies it, with what the call hands
     * it ({@link WorkedOutToReachIt#whereARunMayEndWhereApplied}): each element it is applied to,
     * and for a walk's step every number the walk comes to over the most elements there are.
     */
    private boolean endsNoRunWhereItsClosureIsApplied(Core step) {
        Optional<WhereARunMayStop.Met> met = where.at(step);
        if (met.isEmpty()) {
            return false;
        }
        WhatARunWorksOutBeforeACount.FirstApplication first =
                WhatARunWorksOutBeforeACount.workedOutAtTheFirstApplication(met.get().standsIn(), step);
        if (first == null || first.entered().size() != 1) {
            return false;
        }
        WhatARunWorksOutBeforeACount.Applying applying = first.entered().getFirst();
        return owner.whereARunMayEndWhereApplied(
                new Denotation(applying.call(), met.get().reads()), applying.closure()).isEmpty();
    }

    /**
     * The ways a run gets to {@code step} inside a closure on each application {@code made} that a
     * run makes on some row, in the order a run makes them.
     *
     * <p>Where the step stands inside one closure a call is handed, what a run works out before it
     * on an application is read here: what the call works out before it applies the closure and
     * what the body works out before the step, as on the first application
     * ({@link WhatARunWorksOutBeforeACount#workedOutAtTheFirstApplication}), and each application
     * every run making this one makes before it ({@link #madeInTurn}), whole, whether or not it
     * gets to the step, in the names it was made in. A walk from a seed hands each application
     * after the first what the one before it answered, and the first its seed. Elsewhere what
     * comes before is the way's to say, and is not read.
     */
    private List<Reached> onEachApplication(Core step, WhereARunMayStop.Met met,
                                            WaysToASite.Reach reach,
                                            List<ClosureApplications.Application> made) {
        WhatARunWorksOutBeforeACount.FirstApplication first =
                WhatARunWorksOutBeforeACount.workedOutAtTheFirstApplication(met.standsIn(), step);
        Core.Block closure = (first == null || first.entered().size() != 1) ? null
                : first.entered().getFirst().closure();
        // One application standing for every element a container holds is no one application
        // after another: what it carries in is not the seed. A value looked for at the element
        // holds a list of one, on which it is the first and only one, so what comes before it is
        // what comes before the first.
        boolean forEvery = made.stream().anyMatch(one -> one.held().isEmpty());
        // What a run has worked out by an application, and what it is handed, are read off the
        // applications the run makes of the closure ({@link WhereARunMayStop#applicationsOf}),
        // and never off the ones that get to the step: one that does not get here is worked out
        // all the same, and hands on what it answered.
        List<ClosureApplications.Application> history = (closure == null || forEvery) ? null
                : where.applicationsOf(closure).map(StopsOfABody::madeInTurn).orElse(null);
        List<InputReads> namesOnTheRun = history == null ? null
                : namesOfEachApplication(history, closure);
        List<Reached> out = new ArrayList<>();
        for (ClosureApplications.Application one : made) {
            if (!one.isMadeOnSomeRow()) {
                continue;
            }
            if (forEvery) {
                BeforeAStep before = closure == null ? null
                        : beforeOnTheApplication(reach, first, closure, step, one.reads(),
                                List.of());
                out.add(new Reached(met, reach, one.reads(),
                        ClosureApplications.madeWhateverTheRow(one)
                                || (ClosureApplications.madeOnTheFirstElementWhateverTheRow(one)
                                        && madeOnTheElementAs(one.reached()) != null),
                        before, one.reached(), true));
                continue;
            }
            // Which application of the run this is. One that is none of them is read with
            // nothing before it known, and what comes before it is not read.
            int at = history == null ? -1 : placeAmong(history, one);
            InputReads reads = at < 0 ? one.reads()
                    : handedAsOnTheRun(one.reads(), history, at, namesOnTheRun, closure);
            BeforeAStep before = at < 0 ? null
                    : beforeOnTheApplication(reach, first, closure, step, reads,
                            namesOnTheRun.subList(0, at));
            // Where an operation stops at an answer, what the applications before answered decides
            // whether this one is made, which is what it is held under then.
            boolean onTheWay = closure == null
                    ? ClosureApplications.madeWhateverTheRow(one)
                    : ClosureApplications.madeWhereverTheOnesBeforeItAreGotPast(one);
            out.add(new Reached(met, reach, reads, onTheWay, before, one.reached(), false));
        }
        return out;
    }

    /**
     * Of {@code applications}, the ones a run may make, those whose turn on a run is known: each
     * every run getting past the ones before it makes, whatever the row
     * ({@link ClosureApplications#madeWhereverTheOnesBeforeItAreGotPast}), in turn, without those
     * made on no run, and up to and with the first made only on some rows. After that one, which
     * a run makes next and what it is handed turn on the row, so none of them is placed, and
     * what comes before it is not read.
     */
    static List<ClosureApplications.Application> madeInTurn(
            List<ClosureApplications.Application> applications) {
        List<ClosureApplications.Application> out = new ArrayList<>();
        for (ClosureApplications.Application each : applications) {
            if (!each.isMadeOnSomeRow()) {
                continue;
            }
            out.add(each);
            if (!ClosureApplications.madeWhereverTheOnesBeforeItAreGotPast(each)) {
                break;
            }
        }
        return out;
    }

    /**
     * The names each application of {@code history} is made in on a run: its own, with what a
     * walk from a seed carries into it — the seed into the first, and into each after it what the
     * one before it answered, {@code closure}'s body in that one's names.
     */
    private List<InputReads> namesOfEachApplication(
            List<ClosureApplications.Application> history, Core.Block closure) {
        List<InputReads> out = new ArrayList<>();
        for (int at = 0; at < history.size(); at++) {
            out.add(handedAsOnTheRun(history.get(at).reads(), history, at, out, closure));
        }
        return out;
    }

    /**
     * {@code reads} with what a walk from a seed carries into the {@code at}-th application of
     * {@code history}: the seed where it is the first, and otherwise what the one before it
     * answered, read in {@code namesOnTheRun}'s names for that one.
     */
    private InputReads handedAsOnTheRun(InputReads reads,
                                        List<ClosureApplications.Application> history, int at,
                                        List<InputReads> namesOnTheRun, Core.Block closure) {
        InputReads out = reads;
        for (Map.Entry<BindingId, Denotation> seed
                : history.getFirst().carriedIntoTheFirst().entrySet()) {
            out = out.handing(seed.getKey(), at == 0 ? seed.getValue()
                    : new Denotation(closure.body(), namesOnTheRun.get(at - 1)),
                    read.rules().newtypes());
        }
        return out;
    }

    /** Where {@code one} stands among the applications of {@code history}, by its place among
     *  the applications of each closure it stands in; -1 where it is none of them, or not one
     *  only. */
    private static int placeAmong(List<ClosureApplications.Application> history,
                                  ClosureApplications.Application one) {
        int found = -1;
        for (int at = 0; at < history.size(); at++) {
            if (history.get(at).places().equals(one.places())) {
                if (found >= 0) {
                    return -1;
                }
                found = at;
            }
        }
        return found;
    }

    /**
     * What a run on one application of {@code closure} works out before {@code step}
     * ({@link BeforeAStep#onAnApplication}): what it works out going into the tree the closure
     * stands in, by {@code reach}; each application every run making this one makes before it
     * ({@link #madeInTurn}), whole, in the names {@code earlier} it was made in; what the call
     * works out before it applies the closure and
     * what the body works out up to the step, as on the first application
     * ({@link WhatARunWorksOutBeforeACount#workedOutAtTheFirstApplication}), in this
     * application's names {@code reads} where a part stands in the closure; and then what the
     * step itself is worked out of, as anywhere else ({@link Evaluated#inOrder}). Null where what
     * comes first going in is not read.
     */
    private static BeforeAStep beforeOnTheApplication(
            WaysToASite.Reach reach, WhatARunWorksOutBeforeACount.FirstApplication first,
            Core.Block closure, Core step, InputReads reads, List<InputReads> earlier) {
        List<BeforeAStep.Part> inside = new ArrayList<>();
        earlier.forEach(names -> inside.add(new BeforeAStep.Part(closure.body(), names, true)));
        for (Core part : first.parts().subList(0, first.parts().size() - 1)) {
            inside.add(new BeforeAStep.Part(part, under(closure, part) ? reads : null, true));
        }
        for (Evaluated.Step operand : Evaluated.inOrder(Core.withoutStanding(step))) {
            inside.add(new BeforeAStep.Part(operand.expression(), reads,
                    operand instanceof Evaluated.Step.Always));
        }
        return BeforeAStep.onAnApplication(reach.goingIn().get(), inside).orElse(null);
    }

    /** Whether {@code part} stands inside the body of {@code closure}. */
    private static boolean under(Core.Block closure, Core part) {
        boolean[] found = {false};
        collectUnder(closure.body(), Core.withoutStanding(part), found);
        return found[0];
    }

    private static void collectUnder(Core e, Core part, boolean[] found) {
        if (found[0] || Core.withoutStanding(e) == part) {
            found[0] = true;
            return;
        }
        Core.forEachChild(e, child -> collectUnder(child, part, found));
    }

    // ---- constructions ----

    /**
     * What is shown of {@code made} on every way a run gets to it, each read as an operation's
     * is ({@link #waysTo}): with what it asks read in the names of the way, inside a closure the
     * application's, and with what a run on it works out first, put together as every reader of
     * a step puts its readings ({@link WhatEveryWayShows}).
     */
    private ConstructionStopAssessment.Judgement ofAConstruction(Core.Construct made) {
        Ways ways = waysTo(made);
        return WhatEveryWayShows.together(ways.each().size(),
                at -> ofAConstruction(made, ways.each().get(at)), WhatEveryWayShows::of,
                ways.every(), () -> new ConstructionStopAssessment.Judgement.Unresolved(made,
                        new AConstructionStopNotShown(made.typeName().key(), made.pos(),
                                Optional.empty(), WhyAConstructionStopIsNotShown.REACH_NOT_SHOWN),
                        new WhatAConstructionAsks.OnEveryRule()),
                () -> ofAConstruction(made, null));
    }

    /**
     * What is shown of {@code made} on {@code reached}, one way a run gets to it, or on none.
     *
     * <p>What a run on it works out first is what one application works out where that is read
     * ({@link Reached#before}), and the way's otherwise. A value is looked for on the way only
     * where every run taking it makes the application and nothing it is made under is left
     * unsaid; elsewhere what is shown is only that no run stops there.
     */
    private ConstructionStopAssessment.Judgement ofAConstruction(Core.Construct made,
                                                                 Reached reached) {
        List<AConstructionOnTheWay.Reach> reaches = new ArrayList<>();
        List<SearchRegion> regions = new ArrayList<>();
        if (reached != null) {
            WaysToASite.Reach reach = reached.reach();
            Supplier<Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction>> before =
                    reached.before() == null ? reach.before()
                            : () -> reached.before().asAConstructionReadsIt();
            // One application of many is made where {@link Reached#onTheWay} says; one standing
            // for every element is made under what its element meets, which a value looked for
            // here is not held to, so it is looked for only where that asks nothing.
            boolean madeUnsaid = reached.forEvery()
                    && !(madeOnTheElementAs(reached.made()) instanceof List<?> relations
                            && relations.isEmpty());
            Supplier<Boolean> read = () -> reached.onTheWay() && wayRead(reached) && !madeUnsaid;
            reaches.add(new AConstructionOnTheWay.Reach(0, reach.way(), reach.way(), before,
                    read));
            if (Reachability.of(new WayToTheBorder(reach.way()), this.read.quantities().region())
                    instanceof Reachability.Reaching reaching) {
                regions.add(reaching.region());
            }
        }
        AConstructionOnTheWay one = new AConstructionOnTheWay(made,
                asked(made, reached == null ? null : reached.reads()), reaches, true);
        return ConstructionStopAssessment.ofASite(one, regions, asks(), constructionWays(), read,
                definitions);
    }

    /** What {@code made} asks, read with {@code names}, or with the names as they stand where the
     *  walk met it where that is null. */
    private AConstructionOnTheWay.Asked asked(Core.Construct made, InputReads names) {
        if (ClausesInOrder.at(made, read.rules()).governsNothing()) {
            return new AConstructionOnTheWay.Asked.Nothing();
        }
        Optional<WhereARunMayStop.Met> met = where.at(made);
        if (met.isEmpty()) {
            return new AConstructionOnTheWay.Asked.NotRead();
        }
        return conditions.whereItsOperatorsAnswer(made, names == null ? met.get().reads() : names,
                        read).asks().stream()
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
                        && asked(made, null) instanceof AConstructionOnTheWay.Asked.Read(var ask)) {
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
        if (endsNoRunWhereItsClosureIsApplied(step)) {
            return List.of(new StopAssessment.Judgement.Safe(null,
                    StopAssessment.WhyNone.WITHIN_ITS_ENDS));
        }
        Ways ways = waysTo(step);
        // One figure for the question, spent along every way and every way of its values.
        StopAssessment.Tries tries = new StopAssessment.Tries();
        List<List<StopAssessment.Judgement>> byWay = new ArrayList<>();
        for (Reached each : ways.each()) {
            byWay.add(onAWay(step, each, within, tries));
        }
        return together(byWay, ways.every());
    }

    /**
     * The rows at which every run that gets to {@code step} by some way stops there: where its
     * own operation, over numbers of the input, is past its type
     * ({@link UndividedByARelation#everyRunStopsAt}), within what the way leaves. Said of the
     * runs that get to the step and of no other, so whether every run taking the way gets there
     * is not asked, nor is what it works out before: a run that stops there stops nowhere here.
     */
    private List<EveryRunStops> everyRunStops(Core step) {
        if (endsNoRunWhereItsClosureIsApplied(step)) {
            return List.of();
        }
        Ways ways = waysTo(step);
        if (!ways.areOne()) {
            return List.of();
        }
        Set<EveryRunStops> out = new LinkedHashSet<>();
        for (Reached each : ways.each()) {
            WhatAWayLeavesOfAValue left = WhatAWayLeavesOfAValue.along(read, each.reach().way());
            if (left == null
                    || !(Reachability.of(new WayToTheBorder(each.reach().way()),
                            read.quantities().region()) instanceof Reachability.Reaching reaching)) {
                continue;
            }
            List<StopAssessment.Site> sites = sitesOf(step, each);
            if (sites == null) {
                continue;
            }
            for (StopAssessment.Site site : sites) {
                if (site instanceof StopAssessment.Site.PastItsEnds(var operation)
                        && !left.keepsWithinItsEnds(operation)) {
                    out.addAll(UndividedByARelation.everyRunStopsAt(operation, read,
                            List.of(reaching.region())));
                }
            }
        }
        return List.copyOf(out);
    }

    /**
     * What {@code step} works out of its own on {@code reached}, as operations over numbers of
     * the input: each operation it is ({@link #sitesOf}), and one over values a run works out put
     * as each way a row makes them come to numbers of the input, every way of them, so that what
     * keeps them all within keeps the operation within on every run. Null where some site is a
     * quotient, which no bound on the input keeps from nought, or the ways are not every way.
     */
    private StopEvidence ownWorking(Core step, Reached reached) {
        List<StopAssessment.Site> sites = sitesOf(step, reached);
        if (sites == null) {
            return null;
        }
        List<UndividedByARelation.IntOperation> operations = new ArrayList<>();
        for (StopAssessment.Site site : sites) {
            if (!(site instanceof StopAssessment.Site.PastItsEnds(var operation))) {
                return null;
            }
            Map<NumericTerm, Attainments> worked = new LinkedHashMap<>();
            valuesWorkedOutIn(operation, worked);
            if (worked.isEmpty()) {
                operations.add(operation);
                continue;
            }
            List<Map<NumericTerm, Attainment>> ways = new ArrayList<>();
            if (!waysOf(List.copyOf(worked.keySet()), 0, new LinkedHashMap<>(), new ArrayList<>(),
                    worked, ways, new boolean[1]) || ways.isEmpty()
                    || worked.values().stream().anyMatch(each -> each.ways().isEmpty())) {
                return null;
            }
            ways.forEach(one -> operations.add(atTheWay(operation, one)));
        }
        return new StopEvidence(new UndividedByARelation.Working(operations,
                WhatARelationLeavesUndivided.Told.EVERY), true);
    }

    /** What is shown of {@code step}'s operations by one way a run gets to it. */
    private List<StopAssessment.Judgement> onAWay(Core step, Reached reached,
                                                  List<TakenConstraint.Affine> within,
                                                  StopAssessment.Tries tries) {
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
        if (sites.isEmpty()) {
            return List.of(new StopAssessment.Judgement.Safe(null,
                    StopAssessment.WhyNone.WITHIN_ITS_ENDS));
        }
        List<StopAssessment.Judgement> out = new ArrayList<>();
        for (StopAssessment.Site site : sites) {
            out.add(judgedOn(site, reached, left, within, tries));
        }
        return out;
    }

    /**
     * What a run may stop at in {@code step} itself, with the names as {@code reached} has them:
     * each operation of whole numbers it is, past its ends, and a quotient with its divisor at
     * nought; none where the reading tells none and says every stop there is. Null where it tells
     * none and leaves a stop untold or to another owner, or what a divisor is over is not read.
     */
    private List<StopAssessment.Site> sitesOf(Core step, Reached reached) {
        Core node = Core.withoutStanding(step);
        List<StopAssessment.Site> out = new ArrayList<>();
        // Where the reading of what a run works out tells this node's own operation over numbers
        // the reading answers for, that is it: an element of a list of whole numbers is read
        // there as the number it is, between the ends of the list. One over a part it held aside
        // is over no such number, and is read here from its operands.
        // A number it held aside is the expression it stands for, read here as an operand is.
        List<StopAssessment.Site> told = new ArrayList<>();
        AffineReading.WhatIsWorkedOutBesideWhatIsHeldAside beside =
                evaluatedBeside(node, reached.reads());
        for (UndividedByARelation.IntOperation each : beside.stops().operations().operations()) {
            if (each.origin().node() != node) {
                continue;
            }
            UndividedByARelation.IntOperation read = asReadHere(each, beside.heldAside());
            if (read != null) {
                told.add(new StopAssessment.Site.PastItsEnds(read));
            }
        }
        if (!told.isEmpty()) {
            return told;
        }
        // Told of nothing, a date moved by months stops where the month it lands in is past the
        // calendar, which the reading of the input answers of the node itself.
        if (readsWith.monthsWorkedOut().apply(node, reached.reads())
                instanceof UndividedByARelation.IntOperation months) {
            return List.of(new StopAssessment.Site.PastItsEnds(months));
        }
        // An operation of two Ints is its operator over what its operands come to.
        UndividedByARelation.IntOperation own = ownOperation(node, reached.reads());
        if (own == null) {
            own = ownTotal(node, reached.reads());
        }
        if (own != null) {
            return List.of(new StopAssessment.Site.PastItsEnds(own));
        }
        StopEvidence evidence = evaluated(node, reached.reads());
        // Any other: its own operations, and not those of a step it is worked out of, which are
        // judged there: what the reading of it tells beside what the readings of those tell.
        List<UndividedByARelation.IntOperation> ofWhatItIsMadeOf = new ArrayList<>();
        for (Core under : stepsUnder(node)) {
            ofWhatItIsMadeOf.addAll(evaluated(under, reached.reads()).operations().operations());
        }
        for (UndividedByARelation.IntOperation operation
                : evidence.operations().operations()) {
            if (ofWhatItIsMadeOf.stream().noneMatch(operation::sameOperationAs)) {
                out.add(new StopAssessment.Site.PastItsEnds(operation));
            }
        }
        if (node instanceof Core.Binary quotient
                && AbortSites.ofAnOperator(quotient).contains(AbortKind.DIVISION_BY_ZERO)) {
            LinearForm<NumericTerm> divisor = AffineReading.formOf(quotient.right(),
                    reached.reads(), read, new ElementsMet(),
                    AffineReading.Unkept.EVERY_NAME_AFRESH);
            if (divisor == null) {
                // How many a list written out holds: one number, coming on each way of keeping
                // its elements to how many are kept. Where every way keeps one, nothing stops.
                Attainments count = ownCount(quotient.right(), reached.reads());
                if (count == null) {
                    return null;
                }
                if (!count.leftUnmade() && count.ways().stream().allMatch(way ->
                        way.form().coefs().isEmpty() && !way.form().constant().isZero())) {
                    return out;
                }
                NumericTerm held = heldAs(new Denotation(Core.withoutStanding(quotient.right()),
                        reached.reads()));
                countsHeld.put(held, count);
                divisor = LinearForm.atom(held);
            }
            out.add(new StopAssessment.Site.ByNought(divisor));
        }
        // Nothing of its own told, where the reading says every stop a run may meet in it
        // (StopEvidence#everyStopSaid), is that working it out here stops no run. Where it leaves
        // one untold, or to another owner, nothing here reads it.
        return (out.isEmpty() && !evidence.everyStopSaid()) ? null : out;
    }

    /**
     * {@code operation}, as the reading of what a run works out told it, over what this owner
     * reads of each number in it: a number of the input the reading answers for and a name a
     * container hands it as they are, and a number it held aside as what the expression it stands
     * for comes to as an operand ({@link #operand}). Null where one of them is none of these.
     */
    private UndividedByARelation.IntOperation asReadHere(
            UndividedByARelation.IntOperation operation, Map<NumericTerm, Denotation> heldAside) {
        LinearForm<UndividedByARelation.IntOperand> form = LinearForm.constant(
                operation.form().constant());
        for (Map.Entry<UndividedByARelation.IntOperand, ExactRatio> each
                : operation.form().coefs().entrySet()) {
            LinearForm<UndividedByARelation.IntOperand> one = switch (each.getKey()) {
                case UndividedByARelation.IntOperand.OfTheInput(var term)
                        when heldAside.get(term) instanceof Denotation stands ->
                        operand(stands.value(), stands.at());
                case UndividedByARelation.IntOperand.OfAValueWorkedOut(var term, var _, var _)
                        when heldAside.get(term) instanceof Denotation stands ->
                        operand(stands.value(), stands.at());
                case UndividedByARelation.IntOperand.OfTheInput(var term)
                        when read.quantities().answersFor(term) -> LinearForm.atom(each.getKey());
                case UndividedByARelation.IntOperand.OfABinding _ -> LinearForm.atom(each.getKey());
                default -> null;
            };
            if (one == null || !(one.times(each.getValue()) instanceof ExactAnswer.Held<
                    LinearForm<UndividedByARelation.IntOperand>>(var weighed))
                    || !(form.plus(weighed) instanceof ExactAnswer.Held<
                            LinearForm<UndividedByARelation.IntOperand>>(var sum))) {
                return null;
            }
            form = sum;
        }
        return new UndividedByARelation.IntOperation(form, operation.least(), operation.greatest(),
                operation.after(), operation.ofTheRepresentation(), operation.origin());
    }

    /**
     * The operation of whole numbers {@code node} is, as its operator over what each operand comes
     * to, with the names {@code at} has: a sum, a difference, or a product by a number written, of
     * two {@code Int}s, past the ends of an {@code Int}. Each operand is a form of the input's
     * numbers where it reads as one ({@link AffineReading#formOf}), and otherwise the value its
     * owner says it comes to, from where and by which ways a row makes it
     * ({@link WorkedOutToReachIt#originOf}, {@link WorkedOutToReachIt#attainmentsOf}). Null where
     * it is no such operation, or an operand is neither.
     */
    private UndividedByARelation.IntOperation ownOperation(Core node, InputReads at) {
        if (!(Core.withoutStanding(node) instanceof Core.Binary binary)
                || binary.type() != Type.INT) {
            return null;
        }
        LinearForm<UndividedByARelation.IntOperand> left = operand(binary.left(), at);
        LinearForm<UndividedByARelation.IntOperand> right = operand(binary.right(), at);
        if (left == null || right == null) {
            return null;
        }
        ExactAnswer<LinearForm<UndividedByARelation.IntOperand>> form = switch (binary.op()) {
            case ADD -> left.plus(right);
            case SUB -> left.minus(right);
            case MUL -> right.coefs().isEmpty() ? left.times(right.constant())
                    : left.coefs().isEmpty() ? right.times(left.constant()) : null;
            default -> null;
        };
        if (!(form instanceof ExactAnswer.Held<LinearForm<UndividedByARelation.IntOperand>>(
                var worked))) {
            return null;
        }
        return new UndividedByARelation.IntOperation(worked,
                BigInteger.valueOf(Long.MIN_VALUE), BigInteger.valueOf(Long.MAX_VALUE), List.of(),
                true, new UndividedByARelation.IntOperation.Origin(node));
    }

    /** How many ways of keeping the elements of a list written out a total is read by
     *  ({@link #ownTotal}) before the rest are said untried. */
    private static final int MOST_WAYS_OF_KEEPING = 64;

    /**
     * The total {@code node} works out, where it is a total of whole numbers held to an
     * {@code Int} ({@link GetsPast.WhereTheTotalFits}) over a list written out whose every element
     * reads as a form of the input's numbers: one value, coming on each way of keeping the
     * elements to the sum of those kept, under what keeping each and dropping the others asks of
     * a row ({@link Attainment}), and lying within what each element kept comes to under what
     * keeping it asks, or nought where it may be dropped. A way whose dropping is not read as
     * relations is not made, and is said as left. Null where it is no such total.
     */
    private UndividedByARelation.IntOperation ownTotal(Core node, InputReads at) {
        if (!(Core.withoutStanding(node) instanceof Core.PreservedCall call)
                || call.type() != Type.INT
                || !(WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(call)
                        instanceof GetsPast.WhereTheTotalFits(int list))
                || list >= call.args().size()) {
            return null;
        }
        // Every element kept on every row: the sum of what each comes to as an operand, as an
        // addition of them written out is.
        if (WrittenOutElements.of(new Denotation(call.args().get(list), at),
                read.rules().symbols(), read.rules().newtypes())
                instanceof WrittenOutElements.Walked.Each written
                && written.asWritten().stream().allMatch(each -> each.keptWhere().isEmpty())) {
            LinearForm<UndividedByARelation.IntOperand> sum = LinearForm.constant(ExactRatio.ZERO);
            for (ReadMeaning.Occurrence each : written.asWritten()) {
                LinearForm<UndividedByARelation.IntOperand> one =
                        operand(each.value().value(), each.value().at());
                if (one == null || !(sum.plus(one)
                        instanceof ExactAnswer.Held<LinearForm<UndividedByARelation.IntOperand>>(
                                var added))) {
                    sum = null;
                    break;
                }
                sum = added;
            }
            if (sum != null) {
                return new UndividedByARelation.IntOperation(sum,
                        BigInteger.valueOf(Long.MIN_VALUE), BigInteger.valueOf(Long.MAX_VALUE),
                        List.of(), true, new UndividedByARelation.IntOperation.Origin(node));
            }
        }
        Keeping keeping = keeping(call.args().get(list), at, each -> AffineReading.formOf(
                each.value(), each.at(), read, new ElementsMet(),
                AffineReading.Unkept.EVERY_NAME_AFRESH));
        if (keeping == null) {
            return null;
        }
        // Every element kept on every row: the sum of them, as an addition written out is.
        List<Attainment> ways = keeping.ways().ways();
        LinearForm<UndividedByARelation.IntOperand> form = !keeping.ways().leftUnmade()
                && ways.size() == 1 && ways.getFirst().holding().isEmpty()
                ? ways.getFirst().form().over(term -> LinearForm.atom(
                        new UndividedByARelation.IntOperand.OfTheInput(term)))
                : LinearForm.atom(new UndividedByARelation.IntOperand.OfAValueWorkedOut(
                        heldAs(new Denotation(node, at)),
                        new WhereAValueComesFrom.Derived(keeping.range()), keeping.ways()));
        return new UndividedByARelation.IntOperation(form,
                BigInteger.valueOf(Long.MIN_VALUE), BigInteger.valueOf(Long.MAX_VALUE), List.of(),
                true, new UndividedByARelation.IntOperation.Origin(node));
    }

    /**
     * How many elements {@code node} says a list written out holds, where it is how many a list
     * holds ({@link TakenAs.HowManyItHolds}): on each way of keeping them, as many as are kept
     * ({@link #keeping}). Null where it is no such count.
     */
    private Attainments ownCount(Core node, InputReads at) {
        if (!(Core.withoutStanding(node) instanceof Core.PreservedCall call)
                || call.args().size() != 1
                || !(DefaultBoundOperationFacts.get().takenAs(call.declared().operation())
                        instanceof TakenAs.HowManyItHolds)) {
            return null;
        }
        Keeping keeping = keeping(call.args().getFirst(), at,
                _ -> LinearForm.constant(ExactRatio.ONE));
        return keeping == null ? null : keeping.ways();
    }

    /**
     * What a list written out comes to, each element worth what {@code worth} says, on each way
     * of keeping its elements: the ways ({@link Attainment}), each the sum of what the elements
     * kept are worth under what keeping each and dropping the others asks of a row, and the range
     * that comes to.
     */
    private record Keeping(Attainments ways, FormRange range) {}

    /**
     * {@code listed}, a list written out, as {@link Keeping} says it, or null where it is no list
     * written out, an element's worth is not read, or what keeping one asks is not read as
     * relations of numbers of the input. A way whose dropping is not read so is not made, and is
     * said as left.
     */
    private Keeping keeping(Core listed, InputReads at,
                            Function<Denotation, LinearForm<NumericTerm>> worth) {
        if (!(WrittenOutElements.of(new Denotation(listed, at), read.rules().symbols(),
                read.rules().newtypes()) instanceof WrittenOutElements.Walked.Each written)) {
            return null;
        }
        List<LinearForm<NumericTerm>> forms = new ArrayList<>();
        List<List<TakenConstraint.Affine>> keptBy = new ArrayList<>();
        List<List<List<TakenConstraint.Affine>>> droppedBy = new ArrayList<>();
        FormRange range = new FormRange(ExactRatio.ZERO, ExactRatio.ZERO);
        WhatConditionsState conditions = WhatConditionsState.of(read);
        for (ReadMeaning.Occurrence each : written.asWritten()) {
            LinearForm<NumericTerm> form = worth.apply(each.value());
            if (form == null) {
                return null;
            }
            List<TakenConstraint.Affine> kept = List.of();
            // An element kept whatever the row is dropped on no way.
            List<List<TakenConstraint.Affine>> dropped = List.of();
            if (!each.keptWhere().isEmpty()) {
                // Kept where every condition it is kept by holds, and dropped where any one of
                // them does not.
                List<TakenConstraint.Affine> keptHere = new ArrayList<>();
                List<List<TakenConstraint.Affine>> droppedHere = new ArrayList<>();
                for (ReadMeaning.Occurrence.Kept one : each.keptWhere()) {
                    Proposition asked = conditions.kept(one, read);
                    if (asked instanceof Proposition.Always(boolean holds) && holds) {
                        continue;
                    }
                    List<TakenConstraint.Affine> relations = relationsOf(asked);
                    List<List<TakenConstraint.Affine>> denied = alternativesOf(asked.denied());
                    if (relations == null) {
                        return null;
                    }
                    keptHere.addAll(relations);
                    if (denied == null) {
                        droppedHere = null;
                    } else if (droppedHere != null) {
                        droppedHere.addAll(denied);
                    }
                }
                kept = List.copyOf(keptHere);
                dropped = droppedHere;
            }
            FormRange one = FormRange.of(form, read, boundsUnder(form, kept, true));
            if (one == null) {
                return null;
            }
            range = FormRange.combined(BinOp.ADD, range, each.keptWhere().isEmpty() ? one
                    : one.hull(new FormRange(ExactRatio.ZERO, ExactRatio.ZERO)));
            if (range == null) {
                return null;
            }
            forms.add(form);
            keptBy.add(kept);
            droppedBy.add(dropped);
        }
        List<Attainment> ways = new ArrayList<>();
        boolean left = !waysOfKeeping(forms, keptBy, droppedBy, 0,
                LinearForm.constant(ExactRatio.ZERO), new ArrayList<>(), ways, new boolean[1]);
        return new Keeping(new Attainments(ways, left), range);
    }

    /** Each way of keeping the elements from {@code at} on, after {@code sofar} under
     *  {@code holding}, into {@code out}, as many as {@link #MOST_WAYS_OF_KEEPING}: an element
     *  kept, and dropped by each way its dropping holds ({@link #alternativesOf}). False where
     *  some were left, for the figure or for a dropping not read. */
    private static boolean waysOfKeeping(List<LinearForm<NumericTerm>> forms,
                                         List<List<TakenConstraint.Affine>> keptBy,
                                         List<List<List<TakenConstraint.Affine>>> droppedBy,
                                         int at, LinearForm<NumericTerm> sofar,
                                         List<TakenConstraint.Affine> holding,
                                         List<Attainment> out, boolean[] full) {
        // Past the figure nothing more is made, and nothing more is looked at to make it.
        if (full[0]) {
            return false;
        }
        if (at == forms.size()) {
            if (out.size() >= MOST_WAYS_OF_KEEPING) {
                full[0] = true;
                return false;
            }
            out.add(new Attainment(sofar, List.copyOf(holding)));
            return true;
        }
        boolean all = true;
        if (forms.get(at).plus(sofar) instanceof ExactAnswer.Held<LinearForm<NumericTerm>>(
                var kept)) {
            all = under(keptBy.get(at), holding, () ->
                    waysOfKeeping(forms, keptBy, droppedBy, at + 1, kept, holding, out, full));
        } else {
            all = false;
        }
        if (droppedBy.get(at) == null) {
            return false;
        }
        for (List<TakenConstraint.Affine> dropping : droppedBy.get(at)) {
            all &= under(dropping, holding, () ->
                    waysOfKeeping(forms, keptBy, droppedBy, at + 1, sofar, holding, out, full));
        }
        return all;
    }

    /**
     * What {@code then} answers with {@code more} held beside {@code holding}, which is left as it
     * was; true without asking it where one of {@code more} is the denial of one held, which no row
     * meets both of.
     */
    private static boolean under(List<TakenConstraint.Affine> more,
                                 List<TakenConstraint.Affine> holding, BooleanSupplier then) {
        for (TakenConstraint.Affine each : more) {
            if (holding.contains(new TakenConstraint.Affine(each.form(), each.rel().denied()))) {
                return true;
            }
        }
        int mark = holding.size();
        holding.addAll(more);
        try {
            return then.getAsBoolean();
        } finally {
            holding.subList(mark, holding.size()).clear();
        }
    }

    /**
     * {@code made}, what an application standing for every element a container holds is made
     * under, as the relations of numbers of the input a row meets for it on a list of one element
     * — the list a value looked for at the element is ({@link AValueOfTheInput#ofTheOnlyElement}):
     * that the container holds some element meeting something is that its one element meets it.
     * Null where some part of it is no relation read so.
     */
    private List<TakenConstraint.Affine> madeOnTheElementAs(Proposition made) {
        List<TakenConstraint.Affine> out = new ArrayList<>();
        for (Proposition part : made instanceof Proposition.All(var all, var _, var _) ? all
                : List.of(made)) {
            Proposition asked = (part instanceof Proposition.Some(var _, var element,
                    boolean holds, var _) && holds) ? element : part;
            if (asked instanceof Proposition.Always(boolean holds) && holds) {
                continue;
            }
            List<TakenConstraint.Affine> relations = relationsOf(asked);
            if (relations == null) {
                return null;
            }
            out.addAll(relations);
        }
        return out;
    }

    /**
     * {@code stated}, what an application is made under, as the ways a row meets it at least:
     * each part of a statement that holds where one of them does, each holding the relations of
     * numbers of the input it asks and nothing for what else it asks; one way asking nothing where
     * a part asks nothing read so, since a row may meet the statement there whatever its numbers.
     *
     * <p>An application standing for every element a container keeps is made where the container
     * keeps some element ({@link WhereAClosureIsApplied}), and the element it is made on is one
     * kept: what keeping it asks of that element is what the element meets there.
     */
    private List<List<TakenConstraint.Affine>> alternativesAtLeast(Proposition stated) {
        List<Proposition> parts = stated instanceof Proposition.Any(var any, var _, var _)
                ? any : List.of(stated);
        List<List<TakenConstraint.Affine>> out = new ArrayList<>();
        for (Proposition part : parts) {
            List<TakenConstraint.Affine> relations = new ArrayList<>();
            for (Proposition conjunct : part instanceof Proposition.All(var all, var _, var _)
                    ? all : List.of(part)) {
                Proposition asked = (conjunct instanceof Proposition.Some(var _, var element,
                        boolean holds, var _) && holds) ? element : conjunct;
                for (DemandReading.Read each : DemandReading.asked(asked, read)) {
                    if (each instanceof DemandReading.Read.Demands(
                            RowDemand.Relational(TakenConstraint.Affine affine))) {
                        relations.add(affine);
                    }
                }
            }
            out.add(relations);
        }
        return out;
    }

    /** {@code stated} as the ways a row meets it, each the relations of numbers of the input it
     *  meets: one for each part of a statement that holds where one of them does, or null where
     *  one asks anything else of a row ({@link #relationsOf}). */
    private List<List<TakenConstraint.Affine>> alternativesOf(Proposition stated) {
        List<Proposition> parts = stated instanceof Proposition.Any(var any, var _, var _)
                ? any : List.of(stated);
        List<List<TakenConstraint.Affine>> out = new ArrayList<>();
        for (Proposition part : parts) {
            List<TakenConstraint.Affine> relations = relationsOf(part);
            if (relations == null) {
                return null;
            }
            out.add(relations);
        }
        return out;
    }

    /** {@code stated} as the relations of numbers of the input a row meets for it, or null where
     *  it asks anything else of a row ({@link DemandReading#asked}). */
    private List<TakenConstraint.Affine> relationsOf(Proposition stated) {
        List<TakenConstraint.Affine> out = new ArrayList<>();
        for (DemandReading.Read each : DemandReading.asked(stated, read)) {
            if (each instanceof DemandReading.Read.Demands(
                    RowDemand.Relational(TakenConstraint.Affine affine))) {
                out.add(affine);
            } else if (!(each instanceof DemandReading.Read.Settled(boolean thisWay) && thisWay)) {
                return null;
            }
        }
        return out;
    }

    /** {@code number} moved by {@code by}, or null where that is no number held exactly. */
    private static ExactRatio stepped(ExactRatio number, long by) {
        return number.plus(ExactRatio.of(by)) instanceof ExactAnswer.Held<ExactRatio>(var moved)
                ? moved : null;
    }

    /**
     * The ends of each number of the input {@code form} is over, as a run works it out before
     * any type holds it ({@link FormRange#asWorkedOut}) and as {@code holding} leaves them: a
     * relation of that number alone to a number written narrows them, and any other relation is
     * not read. Where the numbers are {@code whole}, as those an operation of {@code Int}s is over
     * are, a strict relation to a whole number ends one past it, and an end the number is said
     * not to be is the next one in. A number whose ends are not known is held to none, so that a
     * range of the form is none.
     */
    private Map<NumericTerm, FormRange> boundsUnder(LinearForm<NumericTerm> form,
                                                    List<TakenConstraint.Affine> holding,
                                                    boolean whole) {
        Map<NumericTerm, FormRange> out = new HashMap<>();
        for (NumericTerm term : form.coefs().keySet()) {
            FormRange ends = FormRange.asWorkedOut(term, read);
            if (ends == null) {
                out.put(term, null);
                continue;
            }
            ExactRatio least = ends.least();
            ExactRatio greatest = ends.greatest();
            Set<ExactRatio> notAt = new HashSet<>();
            for (TakenConstraint.Affine each : holding) {
                if (each.form().coefs().size() != 1 || !each.form().coefs().containsKey(term)) {
                    continue;
                }
                ExactRatio coef = each.form().coefs().get(term);
                if (!(each.form().constant().negated().dividedBy(coef)
                        instanceof ExactAnswer.Held<ExactRatio>(var bound))) {
                    continue;
                }
                Rel rel = coef.signum() > 0 ? each.rel() : each.rel().turned();
                boolean oneIn = whole && bound.isWhole() && (rel == Rel.GT || rel == Rel.LT);
                ExactRatio from = (oneIn && rel == Rel.GT) ? stepped(bound, 1) : bound;
                ExactRatio to = (oneIn && rel == Rel.LT) ? stepped(bound, -1) : bound;
                if ((rel == Rel.GE || rel == Rel.GT || rel == Rel.EQ) && from != null
                        && (least == null || from.compareTo(least) > 0)) {
                    least = from;
                }
                if ((rel == Rel.LE || rel == Rel.LT || rel == Rel.EQ) && to != null
                        && (greatest == null || to.compareTo(greatest) < 0)) {
                    greatest = to;
                }
                if (rel == Rel.NE && whole && bound.isWhole()) {
                    notAt.add(bound);
                }
            }
            while (greatest != null && notAt.contains(greatest)) {
                greatest = stepped(greatest, -1);
            }
            while (least != null && notAt.contains(least)) {
                least = stepped(least, 1);
            }
            out.put(term, (least == null || greatest == null) ? ends
                    : new FormRange(least, greatest));
        }
        return out;
    }

    /**
     * What {@code operand} comes to as an operand of an operation ({@link #ownOperation}), or
     * null where that is not said: a form of the input's numbers, an operation of two
     * {@code Int}s over what its own operands come to, or a value worked out, held as one number
     * the value's owner says where it comes from.
     */
    private LinearForm<UndividedByARelation.IntOperand> operand(Core operand, InputReads at) {
        LinearForm<NumericTerm> form = AffineReading.formOf(operand, at, read, new ElementsMet(),
                AffineReading.Unkept.EVERY_NAME_AFRESH);
        if (form != null) {
            return form.over(term -> LinearForm.atom(
                    new UndividedByARelation.IntOperand.OfTheInput(term)));
        }
        UndividedByARelation.IntOperation worked = ownOperation(Core.withoutStanding(operand), at);
        if (worked != null) {
            return worked.form();
        }
        LinearForm<UndividedByARelation.IntOperand> ofItsArguments =
                aFormOfItsArguments(Core.withoutStanding(operand), at);
        if (ofItsArguments != null) {
            return ofItsArguments;
        }
        Denotation value = new Denotation(operand, at);
        Attainments ways = attainmentsOf(value, Collections.newSetFromMap(new IdentityHashMap<>()));
        WhereAValueComesFrom origin = owner.originOf(value);
        if (origin == null) {
            origin = comingFrom(ways);
        }
        if (origin == null) {
            return null;
        }
        return LinearForm.atom(new UndividedByARelation.IntOperand.OfAValueWorkedOut(
                heldAs(new Denotation(Core.withoutStanding(operand), at)), origin, ways));
    }

    /**
     * The way to {@code answer} as relations of numbers of the input, where it is a step the walk
     * met once outside every closure: what entering the arm it answers asks, with what the way to
     * the choice asks, as the walk met it — a narrowing to some cases of a position among it. Null
     * where it is not, or a condition of the way is not read so.
     */
    private List<List<TakenConstraint.Affine>> wayToAStepMetOnce(Core answer) {
        Optional<WhereARunMayStop.Met> met = where.at(Core.withoutStanding(answer));
        if (met.isEmpty() || !(met.get().applying() instanceof ClosureApplications.Outside)) {
            return null;
        }
        boolean[] left = {false};
        List<List<TakenConstraint.Affine>> ways =
                StopAssessment.asWaysOfRelations(met.get().way(), left);
        return left[0] ? null : ways;
    }

    /**
     * What {@code node} comes to, where it is a call of an operation declared to answer a form of
     * its arguments, counted as they are ({@link BoundOperationFacts#answersAFormOfItsArguments}):
     * a date moved by days is the day it is moved from and the days. Each argument is read as an
     * operand ({@link #operand}); null where it is no such call or an argument is not read.
     */
    private LinearForm<UndividedByARelation.IntOperand> aFormOfItsArguments(Core node,
                                                                           InputReads at) {
        if (!(Core.withoutStanding(node) instanceof Core.PreservedCall call)) {
            return null;
        }
        LinearForm<DeclaredArgument> declared = DefaultBoundOperationFacts.get()
                .answersAFormOfItsArguments(call.declared().operation());
        if (declared == null) {
            return null;
        }
        LinearForm<UndividedByARelation.IntOperand> out = LinearForm.constant(
                declared.constant());
        for (Map.Entry<DeclaredArgument, ExactRatio> each : declared.coefs().entrySet()) {
            int position = each.getKey().position();
            LinearForm<UndividedByARelation.IntOperand> argument = position < call.args().size()
                    ? operand(call.args().get(position), at) : null;
            if (argument == null || !(argument.times(each.getValue()) instanceof ExactAnswer.Held<
                    LinearForm<UndividedByARelation.IntOperand>>(var weighed))
                    || !(out.plus(weighed) instanceof ExactAnswer.Held<
                            LinearForm<UndividedByARelation.IntOperand>>(var sum))) {
                return null;
            }
            out = sum;
        }
        return out;
    }

    /**
     * Where a value comes from, as the ways a row makes it come to a number say: the numbers each
     * way's form comes to under what the way asks, put together. Null where a way was left unmade
     * or its form's numbers are not known, so that the ways are not every number it may be.
     */
    private WhereAValueComesFrom comingFrom(Attainments ways) {
        if (ways.leftUnmade() || ways.ways().isEmpty()) {
            return null;
        }
        FormRange range = null;
        for (Attainment way : ways.ways()) {
            FormRange one = FormRange.of(way.form(), read,
                    boundsUnder(way.form(), way.holding(), true));
            if (one == null) {
                return null;
            }
            range = range == null ? one : range.hull(one);
        }
        return new WhereAValueComesFrom.Derived(range);
    }

    /**
     * The number a value worked out is held as in an operation over it: named as an author reads
     * it ({@link ComparisonAssessment#written}), and apart from every other value however alike the
     * two read, so that no two values are one number for being written alike. One node with one
     * set of names is one number wherever it is asked; with the names of another application of
     * the closure it stands in, another.
     */
    private NumericTerm heldAs(Denotation value) {
        return heldAs.computeIfAbsent(value, _ -> {
            String written = ComparisonAssessment.written(value.value());
            int alike = writtenAlike.merge(written, 1, Integer::sum);
            return new NumericTerm.ValueOf(TermPath.of(alike == 1 ? written
                    : written + " #" + alike));
        });
    }

    private final Map<Denotation, NumericTerm> heldAs = new HashMap<>();
    private final Map<String, Integer> writtenAlike = new HashMap<>();

    /**
     * Each way a row makes {@code value} come to a number of the input ({@link Attainment}). A
     * {@code let} comes to what its body does, and a name to what it stands for. A choice comes to
     * what each arm answers, on the rows that take the arm: the answer as the walk met it, under
     * what stood on the way to it, the arm's condition among it — and no way of an arm whose way
     * is not a relation of numbers of the input, which no row is shown to take. Anything else is
     * what its owner says ({@link WorkedOutToReachIt#attainmentsOf}). {@code through} holds what is
     * being gone through, so a name reached again says nothing more.
     */
    private Attainments attainmentsOf(Denotation value, Set<Core> through) {
        Core node = Core.withoutStanding(value.value());
        if (!through.add(node)) {
            return Attainments.NONE;
        }
        try {
            if (node instanceof Core.LetIn let) {
                return attainmentsOf(new Denotation(let.body(),
                        value.at().and(let.binder(), let.value())), through);
            }
            if (node instanceof Core.Read) {
                Denotation stands = value.at().standing(node, read.rules().symbols(),
                        read.rules().newtypes());
                if (stands != null && Core.withoutStanding(stands.value()) != node) {
                    return attainmentsOf(stands, through);
                }
            }
            // A form of the input's numbers is what a row makes it, whatever the row.
            LinearForm<NumericTerm> form = AffineReading.formOf(node, value.at(), read,
                    new ElementsMet(), AffineReading.Unkept.EVERY_NAME_AFRESH);
            if (form != null) {
                return Attainments.of(List.of(Attainment.always(form)));
            }
            // A call answering a form of its arguments, each a number of the input: that form.
            if (aFormOfItsArguments(node, value.at()) instanceof LinearForm<
                    UndividedByARelation.IntOperand> ofItsArguments
                    && new UndividedByARelation.IntOperation(ofItsArguments, BigInteger.ZERO,
                            BigInteger.ZERO, List.of(), true,
                            new UndividedByARelation.IntOperation.Origin(node)).overTheInput()
                            instanceof LinearForm<NumericTerm> overTheInput) {
                return Attainments.of(List.of(Attainment.always(overTheInput)));
            }
            Choice choice = Choice.of(node);
            if (choice == null) {
                return owner.attainmentsOf(value);
            }
            // Each arm, on the rows that enter it: what entering it states, read with the names
            // the choice is read with, beside each way its answer comes to a number. An arm
            // whose entering or answer is not read leaves the ways short, which is said.
            List<Attainment> ways = new ArrayList<>();
            boolean leftUnmade = false;
            for (int part = 0; part < choice.arms().size(); part++) {
                Choice.Arm arm = choice.arms().get(part);
                List<List<TakenConstraint.Affine>> entering =
                        alternativesOf(conditions.arm(node, part, value.at()).proposition());
                if (entering == null) {
                    entering = wayToAStepMetOnce(arm.answers());
                }
                Attainments ofTheArm = attainmentsOf(new Denotation(arm.answers(),
                        value.at().choosing(arm.decidedBy(), read.rules().symbols(),
                                read.rules().newtypes())), through);
                if (entering == null || ofTheArm.ways().isEmpty()) {
                    leftUnmade = true;
                    continue;
                }
                leftUnmade |= ofTheArm.leftUnmade();
                for (List<TakenConstraint.Affine> taken : entering) {
                    for (Attainment one : ofTheArm.ways()) {
                        List<TakenConstraint.Affine> holding = new ArrayList<>(one.holding());
                        holding.addAll(taken);
                        ways.add(new Attainment(one.form(), holding));
                    }
                }
            }
            return new Attainments(ways, leftUnmade);
        } finally {
            through.remove(node);
        }
    }

    /** What a run works out evaluating {@code node} with the names {@code at} has, read once for
     *  each, however many steps above it ask. */
    private StopEvidence evaluated(Core node, InputReads at) {
        return evaluatedBeside(node, at).stops();
    }

    /** The same, with what each number the reading held aside stands for. */
    private AffineReading.WhatIsWorkedOutBesideWhatIsHeldAside evaluatedBeside(Core node,
                                                                              InputReads at) {
        return evaluatedAt.computeIfAbsent(new Denotation(node, at), value ->
                AffineReading.stopsOfEvaluatingBesideWhatIsHeldAside(value.value(), value.at(),
                        read, readsWith, owner));
    }

    private final Map<Denotation, AffineReading.WhatIsWorkedOutBesideWhatIsHeldAside> evaluatedAt =
            new HashMap<>();

    /** The steps strictly under {@code node} that the walk met, each judged where it stands. */
    private Set<Core> stepsUnder(Core node) {
        Set<Core> out = Collections.newSetFromMap(new IdentityHashMap<>());
        Core.forEachChild(node, child -> collectSteps(child, out));
        return out;
    }

    private void collectSteps(Core e, Set<Core> out) {
        Core node = Core.withoutStanding(e);
        if (!where.everyPlace(node).isEmpty()) {
            out.add(node);
        }
        Core.forEachChild(node, child -> collectSteps(child, out));
    }

    /** What is shown of {@code site} by one way: none where every value the way leaves keeps it
     *  in, and otherwise a value looked for past what is worked out before it, meeting
     *  {@code within} as well. */
    private StopAssessment.Judgement judgedOn(StopAssessment.Site site, Reached reached,
                                              WhatAWayLeavesOfAValue left,
                                              List<TakenConstraint.Affine> within,
                                              StopAssessment.Tries tries) {
        switch (site) {
            case StopAssessment.Site.PastItsEnds(var operation) -> {
                if (left.keepsWithinItsEnds(operation)) {
                    return new StopAssessment.Judgement.Safe(site,
                            StopAssessment.WhyNone.WITHIN_ITS_ENDS);
                }
            }
            case StopAssessment.Site.ByNought(var divisor) -> {
                // A count held as one number is no place of the input the way leaves anything of.
                if (divisor.coefs().keySet().stream().noneMatch(countsHeld::containsKey)
                        && left.keepsAwayFromNought(divisor)) {
                    return new StopAssessment.Judgement.Safe(site,
                            StopAssessment.WhyNone.DIVISOR_AWAY_FROM_NOUGHT);
                }
            }
        }
        // A run that gets to the site got past what every such run works out first: each of
        // those within its ends is what it meets as well. What only some runs work out is
        // nothing a run getting there need have met.
        GotPast workedOutFirst = gotPastOn(reached, left);
        List<TakenConstraint.Affine> pastFirst = new ArrayList<>(within);
        if (workedOutFirst != null) {
            workedOutFirst.onEveryRun().forEach(each -> pastFirst.addAll(withinItsEnds(each)));
        }
        if (stopsNothingAlongEvery(site, reached, pastFirst)) {
            return new StopAssessment.Judgement.Safe(site,
                    site instanceof StopAssessment.Site.ByNought
                            ? StopAssessment.WhyNone.DIVISOR_AWAY_FROM_NOUGHT
                            : StopAssessment.WhyNone.WITHIN_ITS_ENDS);
        }
        if (!reached.onTheWay() || !wayRead(reached)) {
            return new StopAssessment.Judgement.Unresolved(site,
                    WhyAStopIsNotShown.A_CONDITION_NOT_READ);
        }
        boolean[] waysLeft = {false};
        List<List<TakenConstraint.Affine>> ways =
                StopAssessment.asWaysOfRelations(reached.reach().way(), waysLeft);
        if (ways == null) {
            return new StopAssessment.Judgement.Unresolved(site,
                    WhyAStopIsNotShown.A_CONDITION_NOT_READ);
        }
        GotPast gotPast = gotPastOn(reached, left);
        if (gotPast == null) {
            return new StopAssessment.Judgement.Unresolved(site,
                    WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        }
        // What one application standing for every element is made under, met by the one element
        // of the list a value looked for holds: only where it is over the numbers the site and
        // the way are, so that it is a statement of that element and not of another.
        List<TakenConstraint.Affine> made = List.of();
        if (reached.forEvery()) {
            made = madeOnTheElementAs(reached.made());
            if (made == null || !overTheNumbersOf(made, site, ways)) {
                return new StopAssessment.Judgement.Unresolved(site,
                        WhyAStopIsNotShown.A_CONDITION_NOT_READ);
            }
        }
        // A condition that came out one of several ways is got past along any of them, each way
        // read as one reading of the site ({@link WhatEveryWayShows}).
        List<TakenConstraint.Affine> beside = made;
        return WhatEveryWayShows.together(ways.size(), at -> {
            List<TakenConstraint.Affine> way = new ArrayList<>(ways.get(at));
            way.addAll(beside);
            way.addAll(within);
            return lookedForByEachWay(site, gotPast, left, way, tries);
        }, WhatEveryWayShows::of, !waysLeft[0], () -> new StopAssessment.Judgement.Unresolved(
                site, WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED),
                () -> new StopAssessment.Judgement.Unresolved(site,
                        WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED));
    }

    /** How many ways of the values worked out an operation and what comes before it are over are
     *  put to a search before what is left is said untried: as many as a search for an
     *  assignment on the way tries of one position. */
    private static final int MOST_WAYS_TRIED =
            CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT.maximum();

    /**
     * That a run on {@code way} stops at {@code site} past {@code gotPast}
     * ({@link StopAssessment#aStopLookedFor}), where the operations are over values a run works
     * out as well as numbers of the input: looked for by each way a row makes those values come
     * to numbers of the input ({@link Attainment}), one value being one number wherever it is
     * read, so a way is put in the place of the value in the site and in everything before it
     * alike, and what a row meets for it is put on the way. The first way a stop is shown by is
     * the answer; where none is, the first answer, or that what was left untried may hold one.
     */
    private StopAssessment.Judgement lookedForByEachWay(StopAssessment.Site site, GotPast gotPast,
                                                        WhatAWayLeavesOfAValue left,
                                                        List<TakenConstraint.Affine> way,
                                                        StopAssessment.Tries tries) {
        Map<NumericTerm, Attainments> worked = new LinkedHashMap<>();
        switch (site) {
            case StopAssessment.Site.PastItsEnds(var operation) ->
                    valuesWorkedOutIn(operation, worked);
            case StopAssessment.Site.ByNought(var divisor) -> countsIn(divisor, worked);
        }
        gotPast.operations().forEach(each -> valuesWorkedOutIn(each, worked));
        gotPast.divisors().forEach(each -> countsIn(each, worked));
        if (worked.isEmpty()) {
            if (stopsNothingUnder(site, way)) {
                return new StopAssessment.Judgement.Safe(site,
                        site instanceof StopAssessment.Site.ByNought
                                ? StopAssessment.WhyNone.DIVISOR_AWAY_FROM_NOUGHT
                                : StopAssessment.WhyNone.WITHIN_ITS_ENDS);
            }
            return StopAssessment.aStopLookedFor(site, gotPast.operations(), gotPast.divisors(),
                    left, way, read, tries);
        }
        List<NumericTerm> values = List.copyOf(worked.keySet());
        List<Map<NumericTerm, Attainment>> ways = new ArrayList<>();
        boolean cutShort = !waysOf(values, 0, new LinkedHashMap<>(), new ArrayList<>(way), worked,
                ways, new boolean[1]);
        StopAssessment.Judgement safe = new StopAssessment.Judgement.Safe(site,
                site instanceof StopAssessment.Site.ByNought
                        ? StopAssessment.WhyNone.DIVISOR_AWAY_FROM_NOUGHT
                        : StopAssessment.WhyNone.WITHIN_ITS_ENDS);
        StopAssessment.Judgement untried = new StopAssessment.Judgement.Unresolved(site,
                WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED);
        // Each way of the values is one reading of the site ({@link WhatEveryWayShows}); a value
        // no way is known for leaves the ways short of every one, as a way left untried does. No
        // way at all is no row that meets the way, which stops nothing.
        return WhatEveryWayShows.together(ways.size(), at -> {
            Map<NumericTerm, Attainment> one = ways.get(at);
            List<TakenConstraint.Affine> holding = new ArrayList<>(way);
            one.values().forEach(each -> holding.addAll(each.holding()));
            List<UndividedByARelation.IntOperation> before = new ArrayList<>();
            gotPast.operations().forEach(each -> before.add(atTheWay(each, one)));
            List<LinearForm<NumericTerm>> divisors = new ArrayList<>();
            gotPast.divisors().forEach(each -> divisors.add(atTheWay(each, one)));
            StopAssessment.Site there = switch (site) {
                case StopAssessment.Site.PastItsEnds(var op) ->
                        new StopAssessment.Site.PastItsEnds(atTheWay(op, one));
                case StopAssessment.Site.ByNought(var divisor) ->
                        new StopAssessment.Site.ByNought(atTheWay(divisor, one));
            };
            if (stopsNothingUnder(there, holding)) {
                return safe;
            }
            StopAssessment.Judgement judged = StopAssessment.aStopLookedFor(there, before,
                    divisors, left, holding, read, tries);
            // An operation is said as the sum the way makes it, over numbers of the input; a
            // divisor a way makes a number written is said as it is written.
            return judged instanceof StopAssessment.Judgement.Stops(var shown)
                    && site instanceof StopAssessment.Site.ByNought
                    ? new StopAssessment.Judgement.Stops(shown.ofTheSiteAsWritten(site))
                    : judged;
        }, WhatEveryWayShows::of, !cutShort
                && worked.values().stream().noneMatch(each -> each.ways().isEmpty()),
                () -> untried, () -> safe);
    }

    /** That {@code operation} lies within its ends, as relations of numbers of the input; none
     *  where it is over no form of them. */
    private static List<TakenConstraint.Affine> withinItsEnds(
            UndividedByARelation.IntOperation operation) {
        LinearForm<NumericTerm> form = operation.overTheInput();
        if (form == null
                || !(form.minus(LinearForm.constant(ExactRatio.of(operation.greatest())))
                        instanceof ExactAnswer.Held<LinearForm<NumericTerm>>(var belowTheMost))
                || !(form.minus(LinearForm.constant(ExactRatio.of(operation.least())))
                        instanceof ExactAnswer.Held<LinearForm<NumericTerm>>(var aboveTheLeast))) {
            return List.of();
        }
        return List.of(new TakenConstraint.Affine(belowTheMost, Rel.LE),
                new TakenConstraint.Affine(aboveTheLeast, Rel.GE));
    }

    /** Whether every number {@code relations} are over is one {@code site} or one of
     *  {@code ways} is over. */
    private static boolean overTheNumbersOf(List<TakenConstraint.Affine> relations,
                                            StopAssessment.Site site,
                                            List<List<TakenConstraint.Affine>> ways) {
        Set<NumericTerm> numbers = new HashSet<>();
        switch (site) {
            case StopAssessment.Site.PastItsEnds(var operation) -> {
                if (operation.overTheInput() != null) {
                    numbers.addAll(operation.overTheInput().coefs().keySet());
                }
            }
            case StopAssessment.Site.ByNought(var divisor) -> {
                if (divisor != null) {
                    numbers.addAll(divisor.coefs().keySet());
                }
            }
        }
        ways.forEach(way -> way.forEach(each -> numbers.addAll(each.form().coefs().keySet())));
        return relations.stream().allMatch(each ->
                numbers.containsAll(each.form().coefs().keySet()));
    }

    /**
     * Whether {@code site} stops no run that gets there on {@code reached}: along each way of
     * relations the way to it is ({@link StopAssessment#asWaysOfRelations}), with each way the
     * application it stands in is made under ({@link Reached#made}), and {@code within}, it stops
     * nothing ({@link #stopsNothingUnder}). A run meets everything on the way to get there, so
     * what it meets narrows where it may stop whether or not every run taking the way gets there.
     * False where some of that is not read as relations, or a way was left unmade.
     */
    private boolean stopsNothingAlongEvery(StopAssessment.Site site, Reached reached,
                                           List<TakenConstraint.Affine> within) {
        // What is not read of either is left out: it leaves where a run may go wider.
        boolean[] left = {false};
        List<List<TakenConstraint.Affine>> ways =
                StopAssessment.asWaysOfRelationsAtLeast(reached.reach().way(), left);
        if (left[0]) {
            ways = List.of(List.of());
        }
        List<List<TakenConstraint.Affine>> made = reached.made() == null ? List.of(List.of())
                : alternativesAtLeast(reached.made());
        for (List<TakenConstraint.Affine> way : ways) {
            for (List<TakenConstraint.Affine> one : made) {
                List<TakenConstraint.Affine> holding = new ArrayList<>(way);
                holding.addAll(one);
                holding.addAll(within);
                if (!stopsNothingUnder(site, holding)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Whether {@code site}, over numbers of the input, stops no run meeting {@code holding}: its
     * operation lies within its ends, or its divisor away from nought, over the ends each number
     * it is over has as its declaration and {@code holding} leave them ({@link #boundsUnder}).
     */
    private boolean stopsNothingUnder(StopAssessment.Site site,
                                      List<TakenConstraint.Affine> holding) {
        return switch (site) {
            case StopAssessment.Site.PastItsEnds(var operation) -> {
                LinearForm<NumericTerm> form = operation.overTheInput();
                if (form == null) {
                    yield handedNothingUnder(operation, holding)
                            || withinAtItsEndsUnder(operation, holding);
                }
                FormRange range = FormRange.of(form, read, boundsUnder(form, holding, true));
                yield range != null && range.liesWithin(operation.least(), operation.greatest());
            }
            // A divisor over whole numbers alone, as one of an Int is, is no nearer nought than
            // the next whole number in from a strict relation to it.
            case StopAssessment.Site.ByNought(var divisor) -> {
                FormRange range = divisor == null ? null
                        : FormRange.of(divisor, read, boundsUnder(divisor, holding,
                                divisor.coefs().keySet().stream()
                                        .allMatch(read.quantities().region()::isAnInt)));
                yield range != null && !range.holds(ExactRatio.ZERO);
            }
        };
    }

    /** Whether some name {@code operation} is over that a container hands it
     *  ({@link UndividedByARelation.IntOperand.OfABinding}) is handed nothing on any row meeting
     *  {@code holding}: the greatest it is handed is below the least. No run works it out there. */
    private boolean handedNothingUnder(UndividedByARelation.IntOperation operation,
                                       List<TakenConstraint.Affine> holding) {
        for (UndividedByARelation.IntOperand operand : operation.form().coefs().keySet()) {
            if (operand instanceof UndividedByARelation.IntOperand.OfABinding
                    && operand.atItsEnd(true) instanceof LinearForm<NumericTerm> most
                    && operand.atItsEnd(false) instanceof LinearForm<NumericTerm> least
                    && most.minus(least) instanceof ExactAnswer.Held<LinearForm<NumericTerm>>(
                            var spread)) {
                FormRange range = FormRange.of(spread, read, boundsUnder(spread, holding, true));
                if (range != null && range.greatest().signum() < 0) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Whether {@code operation} lies within its ends at its least and at its greatest over the
     *  values each name it is over is handed ({@link UndividedByARelation.IntOperation#atItsEnd}),
     *  on every row meeting {@code holding}. */
    private boolean withinAtItsEndsUnder(UndividedByARelation.IntOperation operation,
                                         List<TakenConstraint.Affine> holding) {
        for (boolean greatest : List.of(false, true)) {
            LinearForm<NumericTerm> end = operation.atItsEnd(greatest);
            FormRange range = end == null ? null
                    : FormRange.of(end, read, boundsUnder(end, holding, true));
            if (range == null || !range.liesWithin(operation.least(), operation.greatest())) {
                return false;
            }
        }
        return true;
    }

    /** Each value worked out {@code operation} is over, with the ways a row makes it a number,
     *  into {@code out}. */
    private static void valuesWorkedOutIn(UndividedByARelation.IntOperation operation,
                                          Map<NumericTerm, Attainments> out) {
        for (UndividedByARelation.IntOperand each : operation.form().coefs().keySet()) {
            if (each instanceof UndividedByARelation.IntOperand.OfAValueWorkedOut(var atom, var _,
                    Attainments attainments)) {
                out.putIfAbsent(atom, attainments);
            }
        }
    }

    /** Each count held as one number ({@link #countsHeld}) {@code divisor} is over, with the ways
     *  a row makes it a number, into {@code out}. */
    private void countsIn(LinearForm<NumericTerm> divisor, Map<NumericTerm, Attainments> out) {
        if (divisor == null) {
            return;
        }
        for (NumericTerm each : divisor.coefs().keySet()) {
            if (countsHeld.get(each) instanceof Attainments ways) {
                out.putIfAbsent(each, ways);
            }
        }
    }

    /** {@code form} over numbers of the input, each value held as one number put as {@code ways}
     *  says a row makes it; itself where it is over none. */
    private static LinearForm<NumericTerm> atTheWay(LinearForm<NumericTerm> form,
                                                    Map<NumericTerm, Attainment> ways) {
        return form == null ? null : form.over(each -> ways.get(each) instanceof Attainment way
                ? way.form() : LinearForm.atom(each));
    }

    /** How many a list written out holds, where a divisor is over it, held as one number
     *  ({@link #heldAs}), with the ways a row makes it a number ({@link #ownCount}). */
    private final Map<NumericTerm, Attainments> countsHeld = new HashMap<>();

    /** Every way of putting a way of each of {@code values} from {@code at} on, after
     *  {@code sofar} under {@code holding}, into {@code out}, as many as
     *  {@link #MOST_WAYS_TRIED}: none whose relations deny each other ({@link #under}). False
     *  where more were left, or some value's ways were left unmade. */
    private static boolean waysOf(List<NumericTerm> values, int at,
                                  Map<NumericTerm, Attainment> sofar,
                                  List<TakenConstraint.Affine> holding,
                                  Map<NumericTerm, Attainments> worked,
                                  List<Map<NumericTerm, Attainment>> out, boolean[] full) {
        // Past the figure nothing more is made, and nothing more is looked at to make it.
        if (full[0]) {
            return false;
        }
        if (at == values.size()) {
            if (out.size() >= MOST_WAYS_TRIED) {
                full[0] = true;
                return false;
            }
            out.add(Map.copyOf(sofar));
            return true;
        }
        Attainments ways = worked.get(values.get(at));
        boolean all = !ways.leftUnmade();
        for (Attainment way : ways.ways()) {
            sofar.put(values.get(at), way);
            all &= under(way.holding(), holding, () ->
                    waysOf(values, at + 1, sofar, holding, worked, out, full));
            sofar.remove(values.get(at));
        }
        return all;
    }

    /** {@code operation} over numbers of the input, each value worked out it is over put as
     *  {@code ways} says a row makes it; itself where it is over none. */
    private static UndividedByARelation.IntOperation atTheWay(
            UndividedByARelation.IntOperation operation, Map<NumericTerm, Attainment> ways) {
        LinearForm<UndividedByARelation.IntOperand> form = operation.form().over(each ->
                each instanceof UndividedByARelation.IntOperand.OfAValueWorkedOut(var atom, var _,
                        var _) && ways.get(atom) instanceof Attainment way
                        ? way.form().over(term -> LinearForm.atom(
                                new UndividedByARelation.IntOperand.OfTheInput(term)))
                        : LinearForm.atom(each));
        return new UndividedByARelation.IntOperation(form, operation.least(), operation.greatest(),
                operation.after(), operation.ofTheRepresentation(), operation.origin());
    }

    /**
     * What a run works out before a step, read two ways from one account of it.
     *
     * @param operations what a value has to get past to get to the step: each operation a run
     *                   may work out first within its ends, and each divisor away from nought, a
     *                   divisor no form of the input's numbers among them as null — what a value
     *                   shown to stop there, or every run said to, is held to
     * @param onEveryRun the operations of those every run getting to the step works out, and not
     *                   only some: what a run getting there has met, which is all a proof that it
     *                   does not stop there may take as met
     */
    private record GotPast(List<UndividedByARelation.IntOperation> operations,
                           List<LinearForm<NumericTerm>> divisors,
                           List<UndividedByARelation.IntOperation> onEveryRun) {}

    /**
     * What a run on {@code reached} works out before the step ({@link GotPast}): what one
     * application works out, where that is read ({@link Reached#before}), and otherwise what the
     * way says comes first, a part every run works out told from one some runs do. Null where a
     * step in it is not read, or is one a value is not asked of here.
     */
    private GotPast gotPastOn(Reached reached, WhatAWayLeavesOfAValue left) {
        BeforeAStep before = reached.before() != null ? reached.before()
                : reached.reach().before().get().map(BeforeAStep::onTheWay).orElse(null);
        return before == null ? null : gotPastIn(before.parts(), left);
    }

    /**
     * The same, of {@code parts} each worked out with the names it holds, or with the names where
     * the walk met it where it holds none. Of a part every run works out, the steps that run
     * whenever it does are worked out on every run ({@link Evaluated#runningWhenever}); every
     * other step in it, an arm's, is worked out on some.
     */
    private GotPast gotPastIn(List<BeforeAStep.Part> parts, WhatAWayLeavesOfAValue left) {
        List<UndividedByARelation.IntOperation> operations = new ArrayList<>();
        List<LinearForm<NumericTerm>> divisors = new ArrayList<>();
        List<UndividedByARelation.IntOperation> onEveryRun = new ArrayList<>();
        Set<Core> through = Collections.newSetFromMap(new IdentityHashMap<>());
        for (BeforeAStep.Part part : parts) {
            Set<Core> runs = Collections.newSetFromMap(new IdentityHashMap<>());
            if (part.every()) {
                Evaluated.runningWhenever(part.node(), runs);
            }
            if (!past(part.node(), part.names(), left, runs,
                    new GotPast(operations, divisors, onEveryRun), through)) {
                return null;
            }
        }
        return new GotPast(operations, divisors, onEveryRun);
    }

    /**
     * What working out {@code e} asks of a value getting past it, into {@code into}: each step in
     * it that may end a run, read with {@code reads}, as an operation every run works out where it
     * is one of {@code runs}. A function value works out nothing where it is written, and each
     * application of it works out its body where it is applied: a run that gets past an
     * application has got past each step of the body, which is that step's own to show
     * ({@link #stopsNoRunOfItsOwn}). False where a step is not read so.
     */
    private boolean past(Core e, InputReads reads, WhatAWayLeavesOfAValue left, Set<Core> runs,
                         GotPast into, Set<Core> through) {
        Core node = Core.withoutStanding(e);
        // Making a function value works none of its body out; applying one does.
        if (Evaluated.makesAFunction(node)) {
            return true;
        }
        if (!appliesNothingThatStops(node, reads)) {
            return false;
        }
        Core template = definitions.builtBy(node);
        if (template != null) {
            if (!through.add(template)) {
                return false;
            }
            boolean past = past(template, null, left, Set.of(), into, through);
            through.remove(template);
            return past;
        }
        if (node instanceof Core.IfConstructed attempt) {
            boolean[] all = {true};
            WhatARunMayEndFor.forEachWorkedOut(attempt, (part, _) -> all[0] = all[0]
                    && past(part, reads, left, runs, into, through));
            return all[0];
        }
        if (WhereARunMayStop.aStepARunMayStopAt(node)) {
            int from = into.operations().size();
            if (!aStepGotPast(node, reads, left, into.operations(), into.divisors())) {
                return false;
            }
            if (runs.contains(node)) {
                into.onEveryRun().addAll(into.operations().subList(from,
                        into.operations().size()));
            }
        }
        boolean[] all = {true};
        Core.forEachChild(node, child -> all[0] = all[0]
                && past(child, reads, left, runs, into, through));
        return all[0];
    }

    /**
     * Whether every function value {@code node} may apply — one a call is handed, or the one an
     * application applies — has a body every step of which stops no run of its own
     * ({@link #eachStepStopsNoRunOfItsOwn}): a run that gets past the call has got past each
     * application it made. A function value handed by a name is the one the name stands for in
     * {@code reads}; false where the body of one is not known.
     */
    private boolean appliesNothingThatStops(Core node, InputReads reads) {
        List<Core> handed = new ArrayList<>();
        switch (Core.withoutStanding(node)) {
            case Core.Call call -> handed.addAll(call.args());
            case Core.PreservedCall call -> handed.addAll(call.args());
            case Core.Apply apply -> {
                handed.add(apply.fn());
                handed.addAll(apply.args());
            }
            default -> { }
        }
        for (Core each : handed) {
            Core value = Core.withoutStanding(each);
            if (!(TypeView.shapeOf(value.type(), read.rules().inners(), read.rules().symbols(),
                    read.rules().kinds(), read.rules().sums()) instanceof Shape.Function)) {
                continue;
            }
            Denotation named = value instanceof Core.Read && reads != null
                    ? reads.standing(value, read.rules().symbols(), read.rules().newtypes())
                    : null;
            Core function = value instanceof Core.Block ? value
                    : named == null ? null : Core.withoutStanding(named.value());
            if (!(function instanceof Core.Block) || !eachStepStopsNoRunOfItsOwn(function)) {
                return false;
            }
        }
        return true;
    }

    /** Whether every step the walk met in {@code e}, a function value's body among them, stops
     *  no run of its own ({@link #stopsNoRunOfItsOwn}). */
    private boolean eachStepStopsNoRunOfItsOwn(Core e) {
        Core node = Core.withoutStanding(e);
        if (!where.everyPlace(node).isEmpty() && !gotPast(node) && !stopsNoRunOfItsOwn(node)) {
            return false;
        }
        boolean[] all = {true};
        Core.forEachChild(node, child -> all[0] = all[0] && eachStepStopsNoRunOfItsOwn(child));
        return all[0];
    }

    /**
     * Whether no run stops at {@code step}, as what is shown of it says ({@link #stepJudged}):
     * every site of it safe. Not where it is being judged now, which is a step that comes before
     * itself, and is not shown to get past.
     */
    private boolean stopsNoRunOfItsOwn(Core step) {
        AtAStep judged = stepJudged(step);
        return judged != null
                && judged.operations().stream().allMatch(StopAssessment.Judgement.Safe.class::isInstance)
                && judged.construction().map(
                        ConstructionStopAssessment.Judgement.Safe.class::isInstance).orElse(true);
    }

    /**
     * What {@code step}, met where the walk met it once, asks of a value that gets past it, into
     * {@code operations} and {@code divisors}; false where that is not read. Read with
     * {@code reads}, the names of one application of the closure it stands in, and with the names
     * where the walk met it where that is null.
     *
     * <p>Asked whatever premise a run of a row is taken under there: a call of a behavior whose
     * rows get past its body, and an {@code unreachable}, are got past by a row, and a value
     * looked for is no row of either, so it is asked to get past them as any value is.
     */
    private boolean aStepGotPast(Core step, InputReads reads, WhatAWayLeavesOfAValue left,
                                 List<UndividedByARelation.IntOperation> operations,
                                 List<LinearForm<NumericTerm>> divisors) {
        Optional<WhereARunMayStop.Met> met = where.at(step);
        if (met.isEmpty() || gotPast(step)) {
            return false;
        }
        InputReads names = reads == null ? met.get().reads() : reads;
        if (left.endsNoRunAt(new Denotation(step, names))) {
            return true;
        }
        if (Core.withoutStanding(step) instanceof Core.Construct) {
            return false;
        }
        List<StopAssessment.Site> sites = sitesOf(step,
                new Reached(met.get(), null, names, true, null, null, false));
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
     * What every way shows, put together site by site as {@link #ofAnOperation} says: of each
     * kind of site the step has — its own operation past its ends, its divisor at nought, and
     * what is said of the step as a whole — a stop shown by one way, whatever the others come
     * to, and otherwise the first not resolved; and where no way shows or leaves any, none, where
     * the ways are every way, and not resolved where they are not. A stop shown of one site
     * leaves what is not resolved of another said beside it.
     */
    private static List<StopAssessment.Judgement> together(
            List<List<StopAssessment.Judgement>> byWay, boolean every) {
        Map<Object, List<StopAssessment.Judgement>> bySite = new LinkedHashMap<>();
        for (List<StopAssessment.Judgement> way : byWay) {
            for (StopAssessment.Judgement each : way) {
                StopAssessment.Site site = switch (each) {
                    case StopAssessment.Judgement.Stops(var shown) -> shown.site();
                    case StopAssessment.Judgement.Unresolved(var at, var _, var _) -> at;
                    case StopAssessment.Judgement.Safe(var at, var _) -> at;
                };
                bySite.computeIfAbsent(site == null ? StopsOfABody.class : site.getClass(),
                        _ -> new ArrayList<>()).add(each);
            }
        }
        List<StopAssessment.Judgement> out = new ArrayList<>();
        for (List<StopAssessment.Judgement> judged : bySite.values()) {
            StopAssessment.Judgement one = WhatEveryWayShows.together(judged.size(), judged::get,
                    WhatEveryWayShows::of, true, () -> null, () -> null);
            if (!(one instanceof StopAssessment.Judgement.Safe)) {
                out.add(one);
            }
        }
        if (!out.isEmpty()) {
            return out;
        }
        if (!every) {
            return List.of(new StopAssessment.Judgement.Unresolved(null,
                    WhyAStopIsNotShown.REACH_NOT_SHOWN));
        }
        return bySite.isEmpty() ? List.of(new StopAssessment.Judgement.Safe(null,
                StopAssessment.WhyNone.NOT_WORKED_OUT))
                : List.of(bySite.values().iterator().next().getFirst());
    }
}
