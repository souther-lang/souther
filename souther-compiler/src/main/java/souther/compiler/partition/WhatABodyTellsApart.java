package souther.compiler.partition;

import souther.compiler.check.PathReachability;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.inputs.TermPath;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.Decision;
import souther.compiler.reading.NothingAnsweredHere;
import souther.compiler.reading.PathAccess;
import souther.compiler.reading.WayIn;
import souther.compiler.reading.WrittenWithout;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstructOrigin;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The reading {@link BodyDistinction} and {@link ReadTogether} are made by: the ways a body's runs
 * take, each put to the classes of every position it is about.
 *
 * <p><b>A way and not a decision.</b> A decision tells apart only what arrives where it is made. Under
 * {@code guard n > 0} a second {@code guard n > -10} is made of the values the first let through, and
 * comes out the same way for all of them, so it tells nothing apart; read on its own it would split
 * {@code n <= -10} from the values just above it, which no run does. So what a way says about a
 * position is what all of its decisions about that position admit together — the same conjunction
 * a cell is ({@link InteractionCells}) — and a way that admits nothing at some position is one no
 * value takes.
 *
 * <p>Each condition is put to the classes once, however many ways it is on: which position it is
 * about is a walk over the positions, and the ways repeat what holds above a fork for every way out
 * of it.
 */
final class WhatABodyTellsApart {

    /** The ways read so far at one position: what each admitted there, and which comparisons
     *  admitted it. */
    private final List<List<boolean[]>> splits = new ArrayList<>();
    private final List<Set<ModelOccurrence>> comparisonsRead = new ArrayList<>();
    /** Whether some way said something about the position this reading does not put to its
     *  classes. */
    private final boolean[] unread;
    /** Whether some way a run takes holds a decision the reading could name no subject for, which
     *  leaves what is told apart unknown at every position. */
    private boolean subjectUnknown;
    /** The positions measured, with the reading they were measured in — which says where a
     *  condition stands among them ({@link ConditionPlacement}). */
    private final MeasuredInput.MeasuredAxes measured;
    private final List<Axis> axes;
    /** The rules the reading of the input read to the end and found no line in, with why. */
    private final List<RuleWithoutALine> noLine;
    /** The case each arm of a {@code match} is, where the tree the operations stand in names it. */
    private final ArmsNamed armsNamed;
    /** Which positions what decides a fork may turn on, where the same tree reads it. */
    private final ForkDependencies dependencies;
    /** What the model's rules prove arrives at each place a way passes. */
    private final PathReachability.Answers arrives;
    /** Which classes of two positions can be in one value, asked of the positions a way stands
     *  at together. */
    private final ClassCoexistence coexistence;
    /** Which position each condition is about and what it admits there, asked once of each. */
    private final Map<souther.compiler.reading.Condition, Placed> placed = new HashMap<>();
    /** What each way read so far reads together, each once. */
    private final Set<ReadTogether.Way> readTogether = new LinkedHashSet<>();

    private WhatABodyTellsApart(MeasuredInput.MeasuredAxes measured,
                                List<RuleWithoutALine> noLine, ArmsNamed armsNamed,
                                ForkDependencies dependencies,
                                PathReachability.Answers arrives) {
        this.measured = measured;
        this.axes = measured.axes();
        this.noLine = noLine;
        this.armsNamed = armsNamed;
        this.dependencies = dependencies;
        this.arrives = arrives;
        this.coexistence = ClassCoexistence.among(axes);
        this.unread = new boolean[axes.size()];
        for (int at = 0; at < axes.size(); at++) {
            splits.add(new ArrayList<>());
            comparisonsRead.add(new LinkedHashSet<>());
        }
    }

    /**
     * What the body read as {@code read} tells apart at each position {@code measured}, where
     * {@code noLine} is what the reading of the input found about the rules it drew no line for,
     * {@code operationsStanding} what the tree the operations stand in says of the forks, and
     * {@code arrives} what the model's rules prove arrives at each place a way passes.
     */
    static BodyInputReading of(CoverageRead.Read read,
                               MeasuredInput.MeasuredAxes measured,
                               List<RuleWithoutALine> noLine,
                               WhereTheOperationsStand operationsStanding,
                               PathReachability.Answers arrives) {
        WhatABodyTellsApart reading = new WhatABodyTellsApart(measured, noLine,
                operationsStanding.armsNamed(), operationsStanding.dependencies(), arrives);
        WithinOneApplication oneApplication = operationsStanding.oneApplication();
        List<Axis> axes = measured.axes();
        for (WayIn way : read.taken()) {
            reading.take(way, saidInPart(read, way, oneApplication), true);
        }
        // And the ways a run ends, for what a run reads together and nothing else. Each of their
        // decisions is on a way out of its fork already, which is what a position is told apart
        // by; what these add is the decisions made on no one way into a fork and met in the value
        // the run answers, or in a part where it answers nothing.
        // A way already taken was read for both, and read again it would write what it wrote.
        Set<WayIn> taken = new HashSet<>(read.taken());
        for (WayIn way : read.answeredBy()) {
            if (!taken.contains(way)) {
                reading.take(way, saidInPart(read, way, oneApplication), false);
            }
        }
        for (NothingAnsweredHere part : read.answersNothing()) {
            for (List<souther.compiler.reading.Condition> way : part.ways()) {
                reading.takeToAnEnd(way);
            }
        }
        Map<AxisId, BodyDistinction> out = new LinkedHashMap<>();
        List<AxisId> everyOneWith = new ArrayList<>();
        List<AxisId> ids = new ArrayList<>();
        List<List<String>> classes = new ArrayList<>();
        for (int at = 0; at < axes.size(); at++) {
            // A rule the body wrote that no decision reads tells the position apart where no way
            // shows it, and what it reads beside it is not known — whether or not what the ways
            // did read already tells every class apart, which is all the position's own answer
            // asks.
            boolean ruleNoDecisionRead = reading.ruleNoDecisionRead(at);
            if (ruleNoDecisionRead) {
                everyOneWith.add(axes.get(at).id());
            }
            out.put(axes.get(at).id(), reading.at(at, ruleNoDecisionRead));
            ids.add(axes.get(at).id());
            classes.add(axes.get(at).classes().stream().map(PartitionClass::id).toList());
        }
        return new BodyInputReading(out, new ReadTogether.Read(ids, classes,
                List.copyOf(reading.readTogether), everyOneWith));
    }

    /**
     * Whether {@code way} holds less than a run on it decided, as far as which positions the run
     * read together goes.
     *
     * <p>A way inside a function value is written without what the function was called with. Where
     * the fork it goes to is reached within one application of each closure around it
     * ({@link WithinOneApplication}), that is which element the application was handed, and a
     * decision on the element on the way is about the element's position already: what the way
     * says is all that application read together. Anything else it was written without may be a
     * decision on any position, and is what keeps the combinations the way may be part of.
     *
     * <p>A fork inside a closure the walk met where no closure around it kept it from being read
     * one application at a time is one inside a function value the tree the operations stand in
     * holds no closure for, which is a step this reading has no words for.
     */
    private static Set<WhyKept> saidInPart(CoverageRead.Read read, WayIn way,
                                           WithinOneApplication oneApplication) {
        Set<WrittenWithout> without = read.saidInPart().get(way);
        if (without == null) {
            return Set.of();
        }
        Set<WhyKept> out = new LinkedHashSet<>();
        for (WrittenWithout each : without) {
            switch (each) {
                case WrittenWithout.AStep(var why) -> out.add(new WhyKept.AWayReadInPart(why));
                case WrittenWithout.InAFunction(var fork) -> {
                    if (!oneApplication.holdsAt(fork)) {
                        Optional<WhyKept.AFunctionReadAsAWhole> function =
                                oneApplication.readAsAWholeAt(fork);
                        out.add(function.isPresent() ? function.get()
                                : new WhyKept.AWayReadInPart(
                                        PathAccess.Unsupported.Why.RUNS_WHERE_SOMETHING_CALLS_IT));
                    }
                }
            }
        }
        return out;
    }

    /**
     * What one condition says about the positions measured here.
     *
     * <p>The two that place nothing are not one. A condition about something this run measures no
     * position of says nothing about any of them; a condition whose subject the reading could not
     * name may be about any of them, and what it tells apart is not known. Read as one, a decision
     * nothing could place would be a decision about nothing.
     */
    private sealed interface Placed {

        /**
         * About the {@code at}th position.
         *
         * @param admitted the classes it admits there, or null where it admits nothing this
         *                 reading can put to the classes
         */
        record About(int at, List<Boolean> admitted) implements Placed {}

        /**
         * What one application of a closure an operation applies to the elements of a container
         * admits at the element's position: an arm of a {@code match} on what the closure was
         * handed, named a case of it where the operations stand.
         *
         * <p>About one element, which another application of another closure over the same
         * container need not be: two of them on one way are about one element or two, and which
         * is not read, so neither is put to classes there.
         *
         * @param about what the case admits at the element's position
         * @param fork  the fork as the tree that runs has it, which is the application
         */
        record OfAnApplication(About about, ConstructOccurrence fork) implements Placed {}

        /**
         * About the positions {@code ats}, and putting nothing it says there to classes: an arm of
         * a fork whose deciding statement may turn on those positions and no other
         * ({@link ForkDependencies}).
         */
        record AboutThese(List<Integer> ats) implements Placed {}

        /** About nothing this run measures a position of. */
        record AboutNoPosition() implements Placed {}

        /** About something the reading could not name, which may be any of the positions. */
        record SubjectUnknown() implements Placed {}

        /**
         * About a name the cases of a sum share, and so about the position it stands at under
         * whichever case a row is.
         *
         * <p>One answer per case and not one for all of them: a row is one case, and what the
         * condition admits of it is what it admits at that case's position. A row under another
         * case is not at this position at all, so a way admitting nothing here says only that its
         * rows are not this case.
         *
         * @param underEach what the condition says under each case, with what a row is taken to be
         *                  to stand there
         */
        record UnderTheCases(List<UnderACase> underEach) implements Placed {}

        /**
         * What the condition says under one case.
         *
         * @param about      what it admits at the position measured there, or null where no axis
         *                   measures it
         * @param taken      what a row is taken to be for the name to stand there
         * @param neverHolds whether the rules of the case leave the condition no value to come out
         *                   the way the decision went, so that no row of the case takes it
         */
        record UnderACase(About about, Requirements taken, boolean neverHolds) {}
    }

    private Placed placedOf(souther.compiler.reading.Condition condition) {
        return placed.computeIfAbsent(condition, this::placing);
    }

    /** Where {@code each} stands, which is {@link ConditionPlacement}'s answer, and what it admits
     *  there. */
    private Placed placing(souther.compiler.reading.Condition each) {
        // An arm the reading of the runs named no position for, which the tree the operations
        // stand in names as a case of a position: an arm of a `match` on what a closure was handed
        // out of a container. A run down it is one application, handed one element, and the arm
        // admits that element's case: a different case each time is a different application down
        // a different way, and none on an empty container is no run down it at all, which the
        // count the way stands at says ({@link #oneValueCanTake}). Under the cases of a sum the
        // element's position is a choice this does not make, and the arm is put to no class.
        if (each instanceof souther.compiler.reading.Condition.Arm arm) {
            Optional<souther.compiler.reading.Condition.Case> named = armsNamed.of(arm);
            if (named.isPresent()) {
                Placed asTheCase = placing(named.get());
                return asTheCase instanceof Placed.About about
                        ? new Placed.OfAnApplication(about, arm.arm().fork())
                        : withheld(asTheCase);
            }
            // A fork on what an operation over a container answers — `List.all(...)` — or a fork of
            // the operation's own body on what a closure the model handed it answers may turn on
            // the positions what decides it reads, and on no other. Which class went which way is
            // not this arm's to say, so it puts nothing to classes there; a position it cannot
            // turn on is told apart by the ways that do read it.
            Optional<ForkDependencies.Dependency> turnsOn = dependencyOf(arm);
            if (turnsOn.orElse(null) instanceof ForkDependencies.Dependency.Known(var positions)) {
                List<Integer> ats = axesReading(positions);
                return ats.isEmpty() ? new Placed.AboutNoPosition() : new Placed.AboutThese(ats);
            }
        }
        return switch (ConditionPlacement.of(each, measured)) {
            // A fork the reading could not name a subject for: a value no position is, a name bound
            // over several cases, an attempted construction. Which way it goes may turn on any
            // position's value — whether a construction holds its rules can refuse a case of what
            // it is built from — and the condition says nothing of which.
            case ConditionPlacement.Unnamed _ -> new Placed.SubjectUnknown();
            case ConditionPlacement.AtNoPosition _ -> new Placed.AboutNoPosition();
            case ConditionPlacement.AtAPosition(int at) ->
                    about(each, at, InteractionCells.standingOf(each));
            case ConditionPlacement.UnderTheCases(var underEach) -> {
                List<Placed.UnderACase> out = new ArrayList<>();
                for (ConditionPlacement.UnderACase one : underEach) {
                    out.add(new Placed.UnderACase(
                            one.measured() ? about(each, one.axis(), one.at()) : null,
                            one.taken(), neverHolds(each, one.at())));
                }
                yield new Placed.UnderTheCases(List.copyOf(out));
            }
        };
    }

    /**
     * What decides {@code arm}'s fork may turn on: the fork's own, where the model wrote it, and
     * otherwise the construct whose answer decides it — the body of a closure the model handed the
     * operation the fork stands in, or a call of another operation that construct stands for. Empty
     * where none of them was read.
     *
     * <p>A construct of an operation's body stands for that operation's call only where the fork
     * stands outside the operation: inside it, the construct is a part of what the operation
     * computes, and what the call answers is nothing the fork is asked.
     */
    private Optional<ForkDependencies.Dependency> dependencyOf(
            souther.compiler.reading.Condition.Arm arm) {
        Optional<ForkDependencies.Dependency> asWritten =
                ModelOccurrence.statedAt(arm.arm().fork()).flatMap(dependencies::ofTheFork);
        if (asWritten.isPresent() || arm.decidedBy().isEmpty()) {
            return asWritten;
        }
        ConstructOccurrence decides = arm.decidedBy().get();
        Optional<ModelOccurrence> stated = ModelOccurrence.statedAt(decides);
        if (stated.isPresent()) {
            return dependencies.ofTheAnswer(stated.get());
        }
        Optional<ModelOccurrence> called = ModelOccurrence.operationCalledAround(decides);
        return called.isEmpty()
                || called.equals(ModelOccurrence.operationCalledAround(arm.arm().fork()))
                ? Optional.empty() : dependencies.ofTheAnswer(called.get());
    }

    /**
     * {@code placed}, about the same positions and putting nothing it says there to classes: a
     * condition this compiler names the position of and cannot place.
     */
    private static Placed withheld(Placed placed) {
        return switch (placed) {
            case Placed.About it -> new Placed.About(it.at(), null);
            case Placed.UnderTheCases it -> {
                List<Placed.UnderACase> out = new ArrayList<>();
                for (Placed.UnderACase one : it.underEach()) {
                    out.add(new Placed.UnderACase(
                            one.about() == null ? null : new Placed.About(one.about().at(), null),
                            one.taken(), one.neverHolds()));
                }
                yield new Placed.UnderTheCases(List.copyOf(out));
            }
            case Placed.OfAnApplication it -> new Placed.About(it.about().at(), null);
            case Placed.AboutThese it -> it;
            case Placed.AboutNoPosition it -> it;
            case Placed.SubjectUnknown it -> it;
        };
    }

    /**
     * The axes a statement reading {@code positions} may tell values apart at: for each position,
     * the axes at the deepest path it stands at or under — its own, or those of a record measured
     * whole around it.
     *
     * <p>Never an axis below a position. A statement reads what is under a position by naming it,
     * an element as {@code xs[*]}, so a container it names alone is read for how many it holds.
     */
    private List<Integer> axesReading(List<TermPath> positions) {
        Set<Integer> out = new LinkedHashSet<>();
        for (TermPath position : positions) {
            int deepest = -1;
            for (Axis axis : axes) {
                if (position.isAtOrUnder(axis.path())) {
                    deepest = Math.max(deepest, axis.path().steps().size());
                }
            }
            for (int at = 0; at < axes.size(); at++) {
                TermPath measured = axes.get(at).path();
                if (position.isAtOrUnder(measured) && measured.steps().size() == deepest) {
                    out.add(at);
                }
            }
        }
        return List.copyOf(out);
    }

    /**
     * Whether the rules leave {@code each} no value to come out the way it went once the name it is
     * about stands at {@code at}.
     *
     * <p>Asked of the region the rules leave, with the number taken where the name stands under the
     * case — which is what puts the case's own rules on it. Only on a proof: a region that cannot
     * show the comparison is closed there says nothing either way, and the case stays one the row
     * may be. A fork on a case of the value says nothing here; what the case's position admits of it
     * is what its classes say.
     */
    private boolean neverHolds(souther.compiler.reading.Condition each, TermPath at) {
        if (!(each instanceof souther.compiler.reading.Condition.Side side)
                || side.line().isEmpty()
                || !(side.at() instanceof NumericTerm.FromOnePosition named)) {
            return false;
        }
        Quantities quantities = measured.subject().quantities();
        NumericTerm there = quantities.namedAt(named, at);
        NumericTerm.FromOnePosition standing = there == null ? null : there.atOnePosition();
        if (standing == null) {
            return false;
        }
        souther.compiler.reading.Condition.Side.Line line = side.line().get();
        SearchRegion closed = holding(quantities.region(), standing, line.at(),
                line.holding(side.held()));
        return closed != null && closed.emptiness().isPresent();
    }

    /**
     * {@code region} with {@code term rel at} taken in, in the vocabulary a region is told such a
     * thing in: a number as the form with the line moved into it, and a place on an order that
     * counts nothing as an end of the run or a hole in it. Null where the region cannot carry it,
     * which leaves nothing proved.
     */
    private static SearchRegion holding(SearchRegion region, NumericTerm.FromOnePosition term,
                                        Place at, Rel rel) {
        if (at instanceof Count count) {
            LinearForm<NumericTerm> form =
                    LinearForm.atomMinusConstant(term, ExactRatio.of(count.at()));
            return region.assuming(form, rel) instanceof SearchRegion.Assumption.Taken(var taken)
                    ? taken : null;
        }
        return TakenConstraint.Ordered.isABound(rel)
                ? new TakenConstraint.Ordered(term, at, rel).narrowing(region)
                : new TakenConstraint.AwayFrom(term, at).narrowing(region);
    }

    /**
     * What {@code each} admits at the {@code at}th position.
     *
     * @param standing where a case of a value is asked ({@link InteractionCells#admittedAt})
     */
    private Placed.About about(souther.compiler.reading.Condition each, int at,
                               TermPath standing) {
        InteractionCells.Cell cell = InteractionCells.admittedAt(each, axes, at, standing);
        if (cell != null) {
            List<Boolean> admitted = new ArrayList<>();
            for (boolean one : cell.allowed()[at]) {
                admitted.add(one);
            }
            return new Placed.About(at, List.copyOf(admitted));
        }
        // A comparison with no line here, which the reading of the input read to the end and found
        // divides nothing that arrives at it: every value a run brings there goes the same way.
        // Within the way it is on it admits whatever arrives, which rules out nothing the way does
        // not — and read as something unread, every comparison made under another would leave its
        // position one nothing could be said about.
        if (each instanceof souther.compiler.reading.Condition.Side side
                && dividesNothingThatArrives(side, axes.get(at))) {
            return new Placed.About(at,
                    Collections.nCopies(axes.get(at).classes().size(), true));
        }
        return new Placed.About(at, null);
    }

    /** Whether the comparison of {@code side} is one the reading of the input found divides
     *  nothing that arrives at it at {@code axis}. */
    private boolean dividesNothingThatArrives(souther.compiler.reading.Condition.Side side,
                                              Axis axis) {
        ModelOccurrence states = ModelOccurrence.statedAt(side.statedAt()).orElse(null);
        if (states == null) {
            return false;
        }
        for (RuleWithoutALine each : noLine) {
            if (each.rule() instanceof RuleRef.Comparison rule
                    && rule.origin().equals(states.origin())
                    && filedAt(each.at(), axis)
                    && each.why() instanceof BlockReason.ReadToEndWithoutLine read
                    && dividesNothing(read)) {
                return true;
            }
        }
        return false;
    }

    /** Whether a finding filed at {@code at} is about the number {@code axis} measures. */
    private static boolean filedAt(FilingCoordinate at, Axis axis) {
        return switch (at) {
            case FilingCoordinate.AtPosition it -> it.path().equals(axis.path());
            case FilingCoordinate.OfTerm it -> it.term().equals(axis.term());
        };
    }

    /**
     * Whether a rule read to the end with no line sends every value that arrives the same way.
     *
     * <p>Every kind decided here, so that one added later is a decision and not a default. A rule
     * relating two positions, or drawn on a number taken over a run, tells apart something this
     * position's classes are not, and what it does to them is not known.
     */
    private static boolean dividesNothing(BlockReason.ReadToEndWithoutLine why) {
        return switch (why) {
            case BlockReason.ComparisonCuttingNothing _,
                 BlockReason.ComparisonCuttingOutsideDomain _,
                 BlockReason.ComparisonNothingArrivesAtItsLine _,
                 BlockReason.ComparisonLineTurningNothing _,
                 BlockReason.ComparisonRelationNothingArrivesAt _,
                 BlockReason.PredicateTellingNothingApart _ -> true;
            case BlockReason.ComparisonRelatingTwoValues _,
                 BlockReason.ComparisonOverARun _,
                 BlockReason.ComparisonOnARemainder _,
                 BlockReason.RuleRestrictingToAdmittedValues _,
                 BlockReason.ClassesNotComposed _ -> false;
        };
    }

    /** The applications a way holding {@code conditions} goes down, by the element position each
     *  is about. */
    private Map<Integer, Set<ConstructOccurrence>> applicationsAt(
            List<souther.compiler.reading.Condition> conditions) {
        Map<Integer, Set<ConstructOccurrence>> out = new HashMap<>();
        for (souther.compiler.reading.Condition each : conditions) {
            if (placedOf(each) instanceof Placed.OfAnApplication it) {
                out.computeIfAbsent(it.about().at(), _ -> new LinkedHashSet<>()).add(it.fork());
            }
        }
        return out;
    }

    /**
     * One way: what all of its decisions admit together at each position, and which classes of two
     * positions it reads together, if a value can take it.
     *
     * @param saidInPart what the way was written without that holds on it, as what keeps the
     *                   combinations it may be part of; empty where it was written whole
     * @param tellsApart whether what the way admits at each position is part of what the body
     *                   tells apart there, as against only what it reads together
     */
    private void take(WayIn way, Set<WhyKept> saidInPart, boolean tellsApart) {
        // A place on the way the model's rules prove nothing arrives at is one no run passes, so
        // no run takes the way and nothing on it is anything a run decides.
        for (Decision decision : way.decisions()) {
            if (arrives.at(decision.claims().at())
                    instanceof souther.compiler.reach.Reachability.Unreachable) {
                return;
            }
        }
        take(way.conditions(), saidInPart, tellsApart);
    }

    /**
     * A way to a part that answers nothing, held as the conditions on it: which classes of two
     * positions a run there read together before it ended.
     *
     * <p>No run through such a part is watched, so there is no place on the way a proof could be
     * asked of, and it is read as a way some value takes. A combination left owed there is one the
     * account of the obligations says is open on the part.
     */
    private void takeToAnEnd(List<souther.compiler.reading.Condition> conditions) {
        take(conditions, Set.of(), false);
    }

    /** The same of a way held as the conditions on it, once no place on it is proved to be one no
     *  run passes. */
    private void take(List<souther.compiler.reading.Condition> conditions,
                      Set<WhyKept> saidInPart, boolean tellsApart) {
        // What the way says at the positions it stands at whatever case a row is: a condition
        // about the position itself puts a row taking the way there.
        Admitted direct = new Admitted(axes.size());
        boolean subjectUnknownHere = false;
        List<Placed.UnderTheCases> underTheCases = new ArrayList<>();
        List<souther.compiler.reading.Condition> saidUnderTheCases = new ArrayList<>();
        Map<Integer, Set<ConstructOccurrence>> applicationsAt = applicationsAt(conditions);
        for (souther.compiler.reading.Condition each : conditions) {
            switch (placedOf(each)) {
                case Placed.About it -> {
                    direct.stands[it.at()] = true;
                    direct.admit(it, each);
                }
                // An element taking the arm stands at the element's position. Two applications
                // on the way about the same position may be about two elements, so what either
                // admits is read of neither.
                case Placed.OfAnApplication it -> {
                    direct.stands[it.about().at()] = true;
                    direct.admit(applicationsAt.get(it.about().at()).size() > 1
                            ? new Placed.About(it.about().at(), null) : it.about(), each);
                }
                case Placed.UnderTheCases it -> {
                    underTheCases.add(it);
                    saidUnderTheCases.add(each);
                }
                // What a statement reads of a position puts no row there: that no element of a
                // list is `South` is read of the elements and holds of a list with none.
                case Placed.AboutThese it -> {
                    for (int at : it.ats()) {
                        direct.admit(new Placed.About(at, null), each);
                    }
                }
                case Placed.AboutNoPosition _ -> { }
                case Placed.SubjectUnknown _ -> subjectUnknownHere = true;
            }
        }
        for (int at = 0; at < axes.size(); at++) {
            // No class of a position the way stands at takes it, so no value does and nothing on it
            // is anything a run decides.
            if (direct.stands[at] && direct.here[at] != null && !anyOf(direct.here[at])) {
                return;
            }
        }
        // The conditions about names the cases share, read as the cases a row taking the way can
        // be. A row is one case of a sum for every condition on its way, so the conditions are read
        // together as one choice of case and never one at a time: a fork on the flag reached past a
        // comparison only a `Small` can pass tells `Small`'s flag apart and says nothing of
        // `Large`'s. Conditions whose choices touch nothing of each other are chosen apart
        // ({@link CaseChoices}), since a case of one says nothing of the other.
        List<List<Requirements>> takenUnderEach = new ArrayList<>();
        for (Placed.UnderTheCases each : underTheCases) {
            takenUnderEach.add(each.underEach().stream().map(Placed.UnderACase::taken).toList());
        }
        Admitted taken = direct;
        List<Chosen> chosen = new ArrayList<>();
        for (List<Integer> together : CaseChoices.chosenTogether(takenUnderEach)) {
            List<Admitted> ways = waysUnderTheCases(together, underTheCases, saidUnderTheCases,
                    direct);
            // No case leaves a row that takes the way, so none does.
            if (ways.isEmpty()) {
                return;
            }
            Set<Integer> touched = measuredBy(together, underTheCases);
            taken = taken.joinedWith(ways, touched);
            chosen.add(new Chosen(ways, touched));
        }
        // No two positions the way stands at leave classes that can be in one value, so no value
        // takes it: an element's case on the way, and a count of its container that holds nothing.
        if (!oneValueCanTake(taken)) {
            return;
        }
        Set<WhyKept> kept = new LinkedHashSet<>(saidInPart);
        if (subjectUnknownHere) {
            kept.add(new WhyKept.ADecisionNothingNames());
        }
        readTogether(direct, chosen, kept);
        if (!tellsApart) {
            return;
        }
        // Only for a way some value takes. A decision nothing could place is still one no run makes
        // where the rest of its way admits no class.
        subjectUnknown |= subjectUnknownHere;
        for (int at = 0; at < axes.size(); at++) {
            if (taken.here[at] != null) {
                splits.get(at).add(taken.here[at]);
                comparisonsRead.get(at).addAll(taken.stated.get(at));
            }
            unread[at] |= taken.unread[at];
        }
    }

    /**
     * The choices of case one group of conditions leaves a way ({@link CaseChoices}), and the
     * positions they are measured at.
     */
    private record Chosen(List<Admitted> ways, Set<Integer> touched) {}

    /**
     * Which classes of two positions a way reads together, where {@code direct} is what it admits
     * whatever case a row is and {@code chosen} what each group of its conditions about the cases
     * of a sum leaves.
     *
     * <p>A position is read on the way where a decision on it is about the position, whether or not
     * what it said was put to classes. Asked of each choice itself and not of the choices joined:
     * the join is what the way admits at a position, and says nothing of which choice stood there.
     *
     * <p>Two positions under one group are read together a choice at a time, since a row is one
     * choice: a condition under {@code Small} and a condition under {@code Large} are on no run
     * together. Under two groups, or one under a group and one not, the choices of one say nothing
     * of the other, so what each position is read in is taken whole.
     *
     * <p>A way written without something that holds on it, or holding a decision nothing could name
     * the subject of, may read any position besides the ones it names. So every position is read on
     * it, in the classes a row taking it may hold there ({@link #mayHold}) — which is a different
     * question from which classes the choices that read a position read it in, and is answered on
     * its own.
     *
     * <p>Held as ways and never as the combinations they make, which are as many as the product of
     * the positions' classes ({@link ReadTogether.Way}).
     *
     * @param kept what the reading could not say of the way, which is why it is read at every
     *             position; empty where it was read whole
     */
    private void readTogether(Admitted direct, List<Chosen> chosen, Set<WhyKept> kept) {
        int size = axes.size();
        // The group each position is measured under, if one is: -1 where none is, and -2 where
        // more than one is, which is read whole.
        int[] group = new int[size];
        Arrays.fill(group, -1);
        for (int g = 0; g < chosen.size(); g++) {
            for (int at : chosen.get(g).touched()) {
                group[at] = group[at] == -1 ? g : -2;
            }
        }
        List<Integer> noneApart = Collections.nCopies(size, -1);
        if (!kept.isEmpty()) {
            List<BitSet> classes = new ArrayList<>();
            for (int at = 0; at < size; at++) {
                classes.add(classesOf(at, mayHold(at, direct, chosen, group)));
            }
            remember(new ReadTogether.Way(classes, noneApart, kept));
            return;
        }
        // The way whole: each position in the classes the choices that read it read it in, two
        // positions of one group apart.
        List<BitSet> whole = new ArrayList<>();
        List<Integer> apart = new ArrayList<>();
        for (int at = 0; at < size; at++) {
            whole.add(group[at] == -1
                    ? (reads(direct, at) ? classesOf(at, direct.here[at]) : null)
                    : readUnderTheChoices(at, chosen));
            apart.add(Math.max(group[at], -1));
        }
        remember(new ReadTogether.Way(whole, apart, Set.of()));
        // And each choice of a group over the positions only that group is measured at, which is
        // where two positions of the group are read together.
        for (int g = 0; g < chosen.size(); g++) {
            for (Admitted way : chosen.get(g).ways()) {
                List<BitSet> classes = new ArrayList<>();
                for (int at = 0; at < size; at++) {
                    classes.add(group[at] == g && reads(way, at)
                            ? classesOf(at, way.here[at]) : null);
                }
                remember(new ReadTogether.Way(classes, noneApart, Set.of()));
            }
        }
    }

    /** That {@code way} is read, where it reads two positions or more. */
    private void remember(ReadTogether.Way way) {
        if (way.classes().stream().filter(Objects::nonNull).count() > 1) {
            readTogether.add(way);
        }
    }

    /**
     * The classes the choices of case that read the {@code at}th position read it in, or null
     * where none does.
     */
    private BitSet readUnderTheChoices(int at, List<Chosen> chosen) {
        BitSet out = null;
        for (Chosen each : chosen) {
            if (!each.touched().contains(at)) {
                continue;
            }
            for (Admitted way : each.ways()) {
                if (reads(way, at)) {
                    if (out == null) {
                        out = new BitSet();
                    }
                    out.or(classesOf(at, way.here[at]));
                }
            }
        }
        return out;
    }

    /**
     * The classes a row taking the way may hold at the {@code at}th position, null for every class.
     *
     * <p>What the way admits there under each choice of case that is left, and every class under a
     * choice that says nothing of the position: a choice that does not read it leaves it as the row
     * has it. Not which choices read it, which is what a way that says all it holds is read for —
     * one that holds more than it says may read the position under any choice.
     */
    private static boolean[] mayHold(int at, Admitted direct, List<Chosen> chosen, int[] group) {
        if (group[at] == -1) {
            return direct.here[at];
        }
        boolean[] some = null;
        for (Chosen each : chosen) {
            if (!each.touched().contains(at)) {
                continue;
            }
            for (Admitted way : each.ways()) {
                if (!reads(way, at) || way.here[at] == null) {
                    return null;
                }
                if (some == null) {
                    some = new boolean[way.here[at].length];
                }
                for (int c = 0; c < some.length; c++) {
                    some[c] |= way.here[at][c];
                }
            }
        }
        return some;
    }

    /** The classes {@code admitted} names of the {@code at}th position, every class where it is
     *  null. */
    private BitSet classesOf(int at, boolean[] admitted) {
        BitSet out = new BitSet();
        if (admitted == null) {
            out.set(0, axes.get(at).classes().size());
            return out;
        }
        for (int c = 0; c < admitted.length; c++) {
            out.set(c, admitted[c]);
        }
        return out;
    }

    /** Whether a decision on {@code way} is about the {@code at}th position. */
    private static boolean reads(Admitted way, int at) {
        return way.stands[at] || way.unread[at];
    }

    /**
     * Whether every two positions {@code way} stands at leave it a class each that can be in one
     * value ({@link ClassCoexistence}), as the count and the pairs owed ask it. A position the way
     * puts to no class leaves it every class there, and a position with no classes has none to
     * ask about, as it has nothing for a condition to tell apart.
     */
    private boolean oneValueCanTake(Admitted way) {
        for (int one = 0; one < axes.size(); one++) {
            if (!standsInAClass(way, one)) {
                continue;
            }
            for (int other = one + 1; other < axes.size(); other++) {
                if (standsInAClass(way, other) && !somePairHolds(way, one, other)) {
                    return false;
                }
            }
        }
        return true;
    }

    private boolean standsInAClass(Admitted way, int at) {
        return way.stands[at] && !axes.get(at).classes().isEmpty();
    }

    private boolean somePairHolds(Admitted way, int one, int other) {
        for (int here = 0; here < axes.get(one).classes().size(); here++) {
            if (way.here[one] != null && !way.here[one][here]) {
                continue;
            }
            for (int there = 0; there < axes.get(other).classes().size(); there++) {
                if ((way.here[other] == null || way.here[other][there])
                        && coexistence.canHoldTogether(one, here, other, there)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** The positions the conditions {@code together} are measured at under some case. */
    private static Set<Integer> measuredBy(List<Integer> together,
                                           List<Placed.UnderTheCases> underTheCases) {
        Set<Integer> out = new LinkedHashSet<>();
        for (int index : together) {
            for (Placed.UnderACase one : underTheCases.get(index).underEach()) {
                if (one.about() != null) {
                    out.add(one.about().at());
                }
            }
        }
        return out;
    }

    /**
     * Each choice of case the conditions {@code together} leave a row taking the way, with what
     * the way admits under it.
     *
     * <p>A choice stays only where every condition can come out its way under it: its cases go
     * together ({@link Requirements#merge}), they go with the positions the way stands at, the
     * rules of each case leave the condition a value, and the position measured under each admits a
     * class. Which order the conditions are read in leaves the same choices, since each test is
     * one every choice has to pass whatever was read before it.
     */
    private List<Admitted> waysUnderTheCases(List<Integer> together,
                                             List<Placed.UnderTheCases> underTheCases,
                                             List<souther.compiler.reading.Condition> said,
                                             Admitted direct) {
        List<Admitted> ways = List.of(direct);
        for (int index : together) {
            List<Admitted> next = new ArrayList<>();
            for (Admitted way : ways) {
                for (Placed.UnderACase one : underTheCases.get(index).underEach()) {
                    Admitted chosen = way.under(one, said.get(index));
                    if (chosen != null) {
                        next.add(chosen);
                    }
                }
            }
            ways = next;
        }
        return ways;
    }

    /**
     * What a way admits at each position under one choice of case: the classes left, what was said
     * there this reading does not put to classes, the comparisons that said it, which positions a
     * row taking it stands at, and what the row is taken to be.
     */
    private final class Admitted {

        private final boolean[][] here;
        private final boolean[] unread;
        private final List<Set<ModelOccurrence>> stated;
        private final boolean[] stands;
        private final Requirements taken;

        Admitted(int size) {
            this(new boolean[size][], new boolean[size], new ArrayList<>(), new boolean[size],
                    Requirements.NONE);
            for (int at = 0; at < size; at++) {
                stated.add(new LinkedHashSet<>());
            }
        }

        private Admitted(boolean[][] here, boolean[] unread, List<Set<ModelOccurrence>> stated,
                         boolean[] stands, Requirements taken) {
            this.here = here;
            this.unread = unread;
            this.stated = stated;
            this.stands = stands;
            this.taken = taken;
        }

        /** What {@code one}, said by {@code each}, admits, met into what is admitted so far. */
        void admit(Placed.About one, souther.compiler.reading.Condition each) {
            WhatABodyTellsApart.admit(one, each, here, unread, stated);
        }

        /**
         * The same way with the row taken to be the case {@code one} is under, or null where no row
         * of that case takes it.
         */
        Admitted under(Placed.UnderACase one, souther.compiler.reading.Condition each) {
            if (one.neverHolds() || !canBe(one.taken(), here, stands)
                    || !(taken.merge(one.taken())
                            instanceof Requirements.Merge.Merged(Requirements both))) {
                return null;
            }
            Admitted out = new Admitted(copied(here), unread.clone(), copiedSets(stated),
                    stands.clone(), both);
            if (one.about() != null) {
                int at = one.about().at();
                out.stands[at] = true;
                out.admit(one.about(), each);
                // No class of the case's position takes the way, so no row of the case does.
                if (out.here[at] != null && !anyOf(out.here[at])) {
                    return null;
                }
            }
            return out;
        }

        /**
         * This, with what the choices of case {@code ways} admit at the positions {@code touched}
         * they are measured at: a position is admitted in the classes some choice standing there
         * admits it in, and every class where a choice standing there admits every one. Every other
         * position is as this has it, since the choices say nothing of it a case of theirs decides.
         *
         * <p>Where the way stands is not joined. No choice stands at two positions under two cases,
         * and a way standing at both would be read as one no value takes; whether a value takes a
         * choice is asked of the choice ({@link Admitted#under}).
         */
        Admitted joinedWith(List<Admitted> ways, Set<Integer> touched) {
            Admitted out = new Admitted(copied(here), unread.clone(), copiedSets(stated),
                    stands.clone(), taken);
            for (int at : touched) {
                boolean[] some = null;
                boolean everyClass = false;
                for (Admitted way : ways) {
                    if (!way.stands[at]) {
                        continue;
                    }
                    // A row of a choice standing here is here, in the classes the choice admits —
                    // every class where it puts none of them aside.
                    if (way.here[at] == null) {
                        everyClass = true;
                    } else {
                        if (some == null) {
                            some = new boolean[way.here[at].length];
                        }
                        for (int c = 0; c < some.length; c++) {
                            some[c] |= way.here[at][c];
                        }
                    }
                    out.unread[at] |= way.unread[at];
                    out.stated.get(at).addAll(way.stated.get(at));
                }
                if (some != null && !everyClass) {
                    out.here[at] = some;
                }
            }
            return out;
        }
    }

    private static boolean[][] copied(boolean[][] here) {
        boolean[][] out = new boolean[here.length][];
        for (int at = 0; at < here.length; at++) {
            out[at] = here[at] == null ? null : here[at].clone();
        }
        return out;
    }

    private static List<Set<ModelOccurrence>> copiedSets(List<Set<ModelOccurrence>> stated) {
        List<Set<ModelOccurrence>> out = new ArrayList<>();
        for (Set<ModelOccurrence> each : stated) {
            out.add(new LinkedHashSet<>(each));
        }
        return out;
    }

    /** What {@code one}, said by {@code each}, admits, met into what the way admits so far. */
    private static void admit(Placed.About one, souther.compiler.reading.Condition each,
                              boolean[][] here, boolean[] unreadHere,
                              List<Set<ModelOccurrence>> statedHere) {
        if (one.admitted() == null) {
            unreadHere[one.at()] = true;
            return;
        }
        // A position with no classes has nothing for the condition to tell apart, and nothing it
        // admits says whether a value takes the way: that is asked of a position a value at it is
        // in some class of.
        if (one.admitted().isEmpty()) {
            return;
        }
        if (here[one.at()] == null) {
            here[one.at()] = new boolean[one.admitted().size()];
            Arrays.fill(here[one.at()], true);
        }
        for (int c = 0; c < here[one.at()].length; c++) {
            here[one.at()][c] &= one.admitted().get(c);
        }
        if (each instanceof souther.compiler.reading.Condition.Side side) {
            ModelOccurrence.statedAt(side.statedAt()).ifPresent(statedHere.get(one.at())::add);
        }
    }

    /**
     * Whether a row taken to be {@code taken} can take a way that stands at the positions
     * {@code standsHere} marks, in the classes {@code here} leaves them.
     *
     * <p>Asked of each position on its own, as what the way leaves there is: a position stands only
     * where what its path requires holds, and a class of it only where what the class selects holds
     * too — which {@link Requirements#merge} answers, as it does for every reader putting two such
     * requirements together.
     */
    private boolean canBe(Requirements taken, boolean[][] here, boolean[] standsHere) {
        for (int at = 0; at < axes.size(); at++) {
            if (!standsHere[at]) {
                continue;
            }
            Axis axis = axes.get(at);
            if (here[at] == null) {
                if (!taken.compatibleWith(axis.requirements())) {
                    return false;
                }
                continue;
            }
            boolean some = false;
            for (int c = 0; c < here[at].length && !some; c++) {
                some = here[at][c]
                        && taken.compatibleWith(axis.requiring(axis.classes().get(c)));
            }
            if (!some) {
                return false;
            }
        }
        return true;
    }

    private static boolean anyOf(boolean[] admitted) {
        for (boolean each : admitted) {
            if (each) {
                return true;
            }
        }
        return false;
    }

    /**
     * What the ways read tell apart at the {@code at}th position.
     *
     * @param ruleNoDecisionRead whether the body wrote a rule dividing it that no decision the ways
     *                           read is a reading of ({@link #ruleNoDecisionRead(int)})
     */
    private BodyDistinction at(int at, boolean ruleNoDecisionRead) {
        Axis axis = axes.get(at);
        // Unread over anything read. What was read at the position is part of what the body tells
        // apart there, and a part is never said as the whole.
        boolean unplacedHere = unread[at] || ruleNoDecisionRead;
        List<List<String>> groups = groupsOf(axis.classes(), splits.get(at));
        // Unless what was read already tells every class apart, which nothing further can refine:
        // whatever went unread, the partition is the finest there is.
        boolean everyClassApart = !splits.get(at).isEmpty()
                && groups.size() == axis.classes().size();
        if ((subjectUnknown || unplacedHere) && !everyClassApart) {
            return new BodyDistinction.Unread(groups, unplacedHere);
        }
        if (splits.get(at).isEmpty()) {
            return new BodyDistinction.Untouched();
        }
        return new BodyDistinction.Drawn(groups);
    }

    /**
     * Whether the body wrote a rule dividing the {@code at}th position that no decision the ways
     * read is a reading of.
     *
     * <p>What the body wrote that divided the position has to be a rule one of the comparisons read
     * is a reading of. A rule of the type is the model's distinction and not this behavior's, which
     * is the whole question here, so it is not asked for.
     */
    private boolean ruleNoDecisionRead(int at) {
        Axis axis = axes.get(at);
        // A line is filed under the construct its rule is stated at, which is what a decision is
        // filed under too, so the two meet there. A parting — a comparison read for where it parts
        // the values rather than where it cuts them — carries the rule and not the construct, and a
        // comparison's rule is the construct the author wrote, whichever reading of it this was.
        Set<SourceConstructOrigin> written = new LinkedHashSet<>();
        for (ModelOccurrence each : comparisonsRead.get(at)) {
            written.add(each.origin());
        }
        boolean ruleNoDecisionRead = false;
        for (RuleEvidenceOrigin origin : linesAndDivisions(axis)) {
            if (writtenInTheBody(origin.rule())
                    && !(origin instanceof LineOrigin.ComparisonOrigin comparison
                            && comparisonsRead.get(at).contains(comparison.read().states()))) {
                ruleNoDecisionRead = true;
            }
        }
        for (Parting parting : axis.parted()) {
            for (AuthoredLine line : parting.alternatives()) {
                RuleRef rule = line.which().rule();
                ruleNoDecisionRead |= writtenInTheBody(rule)
                        && !(rule instanceof RuleRef.Comparison comparison
                                && written.contains(comparison.origin()));
            }
        }
        return ruleNoDecisionRead;
    }

    /** Every reading of a rule that drew a line on the position or composed its classes. */
    private static List<RuleEvidenceOrigin> linesAndDivisions(Axis axis) {
        List<RuleEvidenceOrigin> out = new ArrayList<>(axis.divides());
        for (Cut cut : axis.cuts()) {
            out.addAll(cut.origins());
        }
        return out;
    }

    /**
     * Whether {@code rule} was written in the body, as against named by the author.
     *
     * <p>A rule the author named — an invariant, an {@code ensures} — says what the type or the
     * answer holds and is no statement about what this behavior tells apart; one written in a body
     * is.
     */
    private static boolean writtenInTheBody(RuleRef rule) {
        return rule instanceof RuleRef.Written;
    }

    /**
     * The classes in groups, two in one group where every way admits both or neither.
     *
     * <p>The coarsest partition finer than what every way admits, which is what telling apart
     * composes to: two classes some way takes one of and not the other are in different groups,
     * however many ways say nothing about them.
     */
    private static List<List<String>> groupsOf(List<PartitionClass> classes,
                                              List<boolean[]> splits) {
        Map<List<Boolean>, List<String>> bySignature = new LinkedHashMap<>();
        for (int c = 0; c < classes.size(); c++) {
            List<Boolean> signature = new ArrayList<>(splits.size());
            for (boolean[] split : splits) {
                signature.add(split[c]);
            }
            bySignature.computeIfAbsent(signature, _ -> new ArrayList<>()).add(classes.get(c).id());
        }
        return List.copyOf(bySignature.values());
    }
}
