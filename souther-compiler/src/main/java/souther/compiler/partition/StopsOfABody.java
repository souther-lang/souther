package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSites;
import souther.compiler.check.ARowsRun;
import souther.compiler.check.Choice;
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
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
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
        this.readsWith = Pullback.whatEveryReadingReadsWith(read);
    }

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
                    each.reads(), read, readsWith);
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
                    read, readsWith));
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
        if (sites.isEmpty()) {
            return List.of(new StopAssessment.Judgement.Safe(null,
                    StopAssessment.WhyNone.WITHIN_ITS_ENDS));
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
     * nought; none where the reading tells none and says every stop there is. Null where it tells
     * none and leaves a stop untold or to another owner, or what a divisor is over is not read.
     */
    private List<StopAssessment.Site> sitesOf(Core step, Reached reached) {
        Core node = Core.withoutStanding(step);
        List<StopAssessment.Site> out = new ArrayList<>();
        // An operation of two Ints is its operator over what its operands come to.
        UndividedByARelation.IntOperation own = ownOperation(node, reached.reads());
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
                return null;
            }
            out.add(new StopAssessment.Site.ByNought(divisor));
        }
        // Nothing of its own told, where the reading says every stop a run may meet in it
        // (StopEvidence#everyStopSaid), is that working it out here stops no run. Where it leaves
        // one untold, or to another owner, nothing here reads it.
        return out.isEmpty() && !evidence.everyStopSaid() ? null : out;
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
        if (!(node instanceof Core.Binary binary) || binary.type() != Type.INT) {
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
        WorkedOutToReachIt owner = WorkedOutToReachIt.of(read);
        Denotation value = new Denotation(operand, at);
        WhereAValueComesFrom origin = owner.originOf(value);
        if (origin == null) {
            return null;
        }
        return LinearForm.atom(new UndividedByARelation.IntOperand.OfAValueWorkedOut(
                heldAs(Core.withoutStanding(operand)), origin,
                attainmentsOf(value, Collections.newSetFromMap(new IdentityHashMap<>()))));
    }

    /**
     * The number a value worked out is held as in an operation over it: named as an author reads
     * it ({@link ComparisonAssessment#written}), and apart from every other value however alike the
     * two read, so that no two values are one number for being written alike. One node is one
     * number wherever it is asked.
     */
    private NumericTerm heldAs(Core node) {
        return heldAs.computeIfAbsent(node, _ -> {
            String written = ComparisonAssessment.written(node);
            int alike = writtenAlike.merge(written, 1, Integer::sum);
            return new NumericTerm.ValueOf(TermPath.of(alike == 1 ? written
                    : written + " #" + alike));
        });
    }

    private final Map<Core, NumericTerm> heldAs = new IdentityHashMap<>();
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
            Choice choice = Choice.of(node);
            if (choice == null) {
                return WorkedOutToReachIt.of(read).attainmentsOf(value);
            }
            List<Attainment> ways = new ArrayList<>();
            boolean leftUnmade = false;
            for (Choice.Arm arm : choice.arms()) {
                for (WhereARunMayStop.Reached met : where.reachedAt(arm.answers())) {
                    List<TakenConstraint.Affine> taken = StopAssessment.asRelations(met.way());
                    if (taken == null) {
                        continue;
                    }
                    Attainments ofTheArm = attainmentsOf(
                            new Denotation(arm.answers(), met.reads()), through);
                    leftUnmade |= ofTheArm.leftUnmade();
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
        return evaluatedAt.computeIfAbsent(new Denotation(node, at), value ->
                AffineReading.stopsOfEvaluating(value.value(), value.at(), read, readsWith));
    }

    private final Map<Denotation, StopEvidence> evaluatedAt = new HashMap<>();

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
        return lookedForByEachWay(site, gotPast, left, way);
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
                                                        List<TakenConstraint.Affine> way) {
        Map<NumericTerm, Attainments> worked = new LinkedHashMap<>();
        if (site instanceof StopAssessment.Site.PastItsEnds(var operation)) {
            valuesWorkedOutIn(operation, worked);
        }
        gotPast.operations().forEach(each -> valuesWorkedOutIn(each, worked));
        if (worked.isEmpty()) {
            return StopAssessment.aStopLookedFor(site, gotPast.operations(), gotPast.divisors(),
                    left, way, read);
        }
        List<NumericTerm> values = List.copyOf(worked.keySet());
        List<Map<NumericTerm, Attainment>> ways = new ArrayList<>();
        boolean cutShort = !waysOf(values, 0, new LinkedHashMap<>(), worked, ways);
        StopAssessment.Judgement first = null;
        for (Map<NumericTerm, Attainment> one : ways) {
            List<TakenConstraint.Affine> holding = new ArrayList<>(way);
            one.values().forEach(each -> holding.addAll(each.holding()));
            List<UndividedByARelation.IntOperation> before = new ArrayList<>();
            gotPast.operations().forEach(each -> before.add(atTheWay(each, one)));
            StopAssessment.Site there = site instanceof StopAssessment.Site.PastItsEnds(var op)
                    ? new StopAssessment.Site.PastItsEnds(atTheWay(op, one)) : site;
            StopAssessment.Judgement judged = StopAssessment.aStopLookedFor(there, before,
                    gotPast.divisors(), left, holding, read);
            if (judged instanceof StopAssessment.Judgement.Stops) {
                return judged;
            }
            if (first == null) {
                first = judged;
            }
        }
        return first == null || cutShort
                ? new StopAssessment.Judgement.Unresolved(site,
                        WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED)
                : first;
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

    /** Every way of putting a way of each of {@code values} from {@code at} on, after
     *  {@code sofar}, into {@code out}, as many as {@link #MOST_WAYS_TRIED}; false where more were
     *  left, or some value's ways were left unmade. */
    private static boolean waysOf(List<NumericTerm> values, int at,
                                  Map<NumericTerm, Attainment> sofar,
                                  Map<NumericTerm, Attainments> worked,
                                  List<Map<NumericTerm, Attainment>> out) {
        if (at == values.size()) {
            if (out.size() >= MOST_WAYS_TRIED) {
                return false;
            }
            out.add(Map.copyOf(sofar));
            return true;
        }
        Attainments ways = worked.get(values.get(at));
        boolean all = !ways.leftUnmade();
        for (Attainment way : ways.ways()) {
            sofar.put(values.get(at), way);
            all &= waysOf(values, at + 1, sofar, worked, out);
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

    /**
     * What {@code step}, met where the walk met it once, asks of a value that gets past it, into
     * {@code operations} and {@code divisors}; false where that is not read.
     *
     * <p>Asked whatever premise a run of a row is taken under there: a call of a behavior whose
     * rows get past its body, and an {@code unreachable}, are got past by a row, and a value
     * looked for is no row of either, so it is asked to get past them as any value is.
     */
    private boolean aStepGotPast(Core step, WhatAWayLeavesOfAValue left,
                                 List<UndividedByARelation.IntOperation> operations,
                                 List<LinearForm<NumericTerm>> divisors) {
        Optional<WhereARunMayStop.Met> met = where.at(step);
        if (met.isEmpty() || gotPast(step)) {
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
