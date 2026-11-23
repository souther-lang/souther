package souther.compiler.partition;

import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.ValueTemplates;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.inputs.AConstructionStopNotShown;
import souther.compiler.inputs.AConstructionStopShown;
import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatAConstructionAsks;
import souther.compiler.inputs.WhyAConstructionStopIsNotShown;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumberSpace;
import souther.compiler.numeric.NumericDomain;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.IntFunction;
import java.util.function.Predicate;

/**
 * Whether a run on the way to a comparison stops at each construction it may work out before it:
 * shown not to, shown to, or neither — what {@link StopAssessment} answers of an operation,
 * answered of a construction.
 *
 * <p>{@link Judgement.Safe} is a proof that every run taking the way to the comparison and getting
 * to the construction meets what it asks: it asks nothing, the way to the comparison and to the
 * construction holds it, no row takes both, or a construction every such run has got past by then
 * asks as much. {@link Judgement.Stops} is a proof that some run does not, and rests on one value
 * of the input that exists ({@link AValueOfTheInput}), meets every condition on the way to the
 * comparison and on the way to the construction, gets to the construction with nothing before it
 * ending the run, and does not meet what it asks. {@link Judgement.Unresolved} is everything else,
 * with the first of those the proof could not rest on
 * ({@link WhyAConstructionStopIsNotShown}).
 *
 * <p>Getting to it is shown where a run that takes the way to the comparison and the way to the
 * construction works the construction out before the comparison unless something before it ends
 * the run ({@link WhatARunWorksOutBeforeACount#workedOutBeforeAConstruction}), every condition on
 * those ways is a relation of numbers of the input or settled, and everything a run may work out
 * before it ends no run whatever the input ({@link WhatARunMayEndFor}) or is a construction whose
 * condition is read over numbers of the input, which the value is then asked to meet. The way to
 * a construction on an arm is the arm's condition with what stood above it, as the walk met it
 * ({@link WhereConstructionsAreMet}). What a construction asks is where making its type succeeds,
 * and nothing narrower or wider ({@link DeclaredBounds#whereMakingSucceeds}), so a value meeting it
 * gets past the construction and one that does not stops there.
 *
 * <p>Asked of the way to the comparison, as what is said of the construction is said of the rule:
 * a run that does not take that way is a run to some other rule.
 *
 * <p>Asked of every construction a run on the way may work out before the comparison
 * ({@link ComparisonReadings.Reading#onTheWay}), whatever is read of it: one whose condition is not
 * read, or whose way is not, is unresolved for that reason, and never left out.
 */
final class ConstructionStopAssessment {

    private ConstructionStopAssessment() {}

    /** How many values of the input are put to the proof of one construction before it is left
     *  unresolved: as many as a search for an assignment on the way tries of one position. */
    private static final int MOST_VALUES_TRIED =
            CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT.maximum();

    /** What is shown of one construction. */
    sealed interface Judgement {

        /** The construction it is of. */
        Core.Construct made();

        /** Every run getting to it meets what it asks; nothing is said of it. */
        record Safe(Core.Construct made) implements Judgement {}

        /** Some run on the way stops at the construction {@code shown} names. */
        record Stops(Core.Construct made, Shown shown) implements Judgement {}

        /**
         * Neither is shown: {@code told} is what it asks that the way does not hold, where that is
         * read, and why, and {@code bearing} which rules it is said under.
         */
        record Unresolved(Core.Construct made, AConstructionStopNotShown told,
                          WhatAConstructionAsks.Bearing bearing) implements Judgement {}
    }

    /** Which rules what is said of {@code judged}, a construction a run stops at or one of which
     *  neither is shown, is said under; null where nothing is said of it. */
    static WhatAConstructionAsks.Bearing bearingOf(Judgement judged) {
        return switch (judged) {
            case Judgement.Safe _ -> null;
            case Judgement.Stops(var _, Shown shown) -> shown.told().bearing();
            case Judgement.Unresolved(var _, var _, WhatAConstructionAsks.Bearing bearing) ->
                    bearing;
        };
    }

    /**
     * That a run on the way stops at a construction: the value of the input {@link #at}, a whole
     * number at each place it is asked of, exists, takes the way, gets to the construction and does
     * not meet what it asks ({@link #told}). Made here and nowhere else, and only once all of that
     * is shown.
     */
    static final class Shown {

        private final WhatAConstructionAsks told;
        private final Map<NumericTerm, ExactRatio> at;

        private Shown(WhatAConstructionAsks told, Map<NumericTerm, ExactRatio> at) {
            this.told = told;
            this.at = Map.copyOf(at);
        }

        WhatAConstructionAsks told() {
            return told;
        }

        Map<NumericTerm, ExactRatio> at() {
            return at;
        }

        @Override
        public String toString() {
            return told.construction().qualified() + " at " + told.at() + " for " + at;
        }
    }

    /**
     * What is shown of each construction a run on the way to the comparison {@code each} reads may
     * work out before it ({@link ComparisonReadings.Reading#onTheWay}), where every row taking the
     * way to it is in one of {@code ways}: in the order they are worked out.
     */
    static List<Judgement> of(ComparisonReadings.Reading each, List<SearchRegion> ways,
                              InputReading read) {
        List<AConstructionOnTheWay> onTheWay = each.onTheWay();
        List<ConstructionAsk> asks = new ArrayList<>();
        // The way to each construction by each way into the body the comparison stands in.
        Map<Integer, Map<Core, List<OnTheWay>>> waysTo = new HashMap<>();
        for (AConstructionOnTheWay one : onTheWay) {
            if (one.asked() instanceof AConstructionOnTheWay.Asked.Read(ConstructionAsk ask)) {
                asks.add(ask);
            }
            for (AConstructionOnTheWay.Reach reach : one.reaches()) {
                waysTo.computeIfAbsent(reach.entry(), _ -> new IdentityHashMap<>())
                        .put(one.made(), reach.toIt());
            }
        }
        // Whether the way holds a part is asked of each part once, however many times it is read.
        Predicate<Proposition> toTheComparison = heldOnEvery(ways, read);
        List<Judgement> out = new ArrayList<>();
        for (AConstructionOnTheWay one : onTheWay) {
            out.add(switch (one.asked()) {
                case AConstructionOnTheWay.Asked.Nothing _ -> new Judgement.Safe(one.made());
                // Not read for want of the names where it is worked out, where the walk did not
                // meet it on one way: that no run is shown to get to it is what is missing.
                case AConstructionOnTheWay.Asked.NotRead _ -> new Judgement.Unresolved(one.made(),
                        new AConstructionStopNotShown(one.made().typeName().key(),
                                one.made().pos(), Optional.empty(), !one.reaches().isEmpty()
                                        ? WhyAConstructionStopIsNotShown.ASKS_NOT_READ
                                        : WhyAConstructionStopIsNotShown.REACH_NOT_SHOWN),
                        new WhatAConstructionAsks.OnEveryRule());
                case AConstructionOnTheWay.Asked.Read(ConstructionAsk ask) ->
                        judged(one, ask, asks, waysTo, toTheComparison, read,
                                each.definitions());
            });
        }
        return out;
    }

    /**
     * What is shown of {@code one}, which asks {@code ask}, among constructions that ask
     * {@code asks} and are met on the ways {@code waysTo} holds by each way in, where the way to
     * the comparison holds what {@code toTheComparison} says.
     *
     * <p>Asked by each way a run on the way gets to it on, and put together: a stop shown by one
     * of them is a run that stops, whatever the others come to; safe only where every one is and
     * they are every way there is; otherwise not resolved, for the first reason one of them gives,
     * or, where each one read is safe, because some way is not read.
     */
    private static Judgement judged(AConstructionOnTheWay one, ConstructionAsk ask,
                                    List<ConstructionAsk> asks,
                                    Map<Integer, Map<Core, List<OnTheWay>>> waysTo,
                                    Predicate<Proposition> toTheComparison, InputReading read,
                                    ValueTemplates definitions) {
        // What asks nothing, or nothing the way to the comparison does not hold, is safe whatever
        // the tree says, and the tree is walked only for what is left.
        Optional<WhatAConstructionAsks> unheld =
                ask.toldOf(is -> toTheComparison.test(is.read()));
        if (unheld.isEmpty()) {
            return new Judgement.Safe(one.made());
        }
        List<Judgement> judged = new ArrayList<>();
        Together shown = together(one.reaches().size(), at -> {
            AConstructionOnTheWay.Reach reach = one.reaches().get(at);
            Judgement byIt = judgedOn(one, reach, ask, asks,
                    waysTo.getOrDefault(reach.entry(), Map.of()), toTheComparison, read,
                    definitions);
            judged.add(byIt);
            return switch (byIt) {
                case Judgement.Safe _ -> ByAWay.SAFE;
                case Judgement.Stops _ -> ByAWay.STOPS;
                case Judgement.Unresolved _ -> ByAWay.NOT_RESOLVED;
            };
        }, one.everyWay());
        return switch (shown) {
            case Together.ByOne(int at) -> judged.get(at);
            case Together.NoneStops _ -> new Judgement.Safe(one.made());
            case Together.ByAWayNotRead _ ->
                    unresolved(one, ask, unheld, WhyAConstructionStopIsNotShown.REACH_NOT_SHOWN);
        };
    }

    /** What one way a run gets to a construction on shows of it. */
    enum ByAWay { SAFE, STOPS, NOT_RESOLVED }

    /** What is shown of a construction, put together from each way a run gets to it on
     *  ({@link #together}). */
    sealed interface Together {

        /** What the {@code at}-th way shows. */
        record ByOne(int at) implements Together {}

        /** That no run on the way stops there: every way is read, and each shows it. */
        record NoneStops() implements Together {}

        /** Not resolved, since each way read shows no run stops there and some way is not
         *  read. */
        record ByAWayNotRead() implements Together {}
    }

    /**
     * What is shown of a construction, from what each of {@code ways} ways a run gets to it on
     * shows ({@code shownBy}, asked of each in turn, and of none past a stop): the first stop,
     * whatever the others come to, since one run that stops is a run that stops; otherwise the
     * first not resolved; otherwise, where they are every way there is ({@code everyWay}), that
     * none stops; and otherwise not resolved, for want of the way not read. Safe asks of every run,
     * and a stop of one.
     */
    static Together together(int ways, IntFunction<ByAWay> shownBy, boolean everyWay) {
        int unresolved = -1;
        for (int at = 0; at < ways; at++) {
            switch (shownBy.apply(at)) {
                case STOPS -> {
                    return new Together.ByOne(at);
                }
                case NOT_RESOLVED -> {
                    if (unresolved < 0) {
                        unresolved = at;
                    }
                }
                case SAFE -> { }
            }
        }
        if (unresolved >= 0) {
            return new Together.ByOne(unresolved);
        }
        return everyWay ? new Together.NoneStops() : new Together.ByAWayNotRead();
    }

    /** What is shown of {@code one} by {@code reach}, one way a run on the way gets to it on
     *  ({@link #judged}). */
    private static Judgement judgedOn(AConstructionOnTheWay one,
                                      AConstructionOnTheWay.Reach reach, ConstructionAsk ask,
                                      List<ConstructionAsk> asks, Map<Core, List<OnTheWay>> waysTo,
                                      Predicate<Proposition> toTheComparison, InputReading read,
                                      ValueTemplates definitions) {
        Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction> before = reach.before().get();
        if (before.isEmpty()) {
            return unresolved(one, ask, ask.toldOf(is -> toTheComparison.test(is.read())),
                    WhyAConstructionStopIsNotShown.REACH_NOT_SHOWN);
        }
        // The way to the comparison and the way to the construction, both of which a run that
        // gets to it on the way to the comparison takes.
        List<OnTheWay> both = new ArrayList<>(reach.toTheComparison());
        for (OnTheWay entry : reach.toIt()) {
            if (!both.contains(entry)) {
                both.add(entry);
            }
        }
        Predicate<Proposition> toIt = toTheComparison;
        if (both.size() > reach.toTheComparison().size()) {
            Reachability taken = Reachability.of(new WayToTheBorder(both),
                    read.quantities().region());
            if (!taken.leavesARow()) {
                return new Judgement.Safe(one.made());
            }
            toIt = heldOnEvery(taken instanceof Reachability.Reaching reaching
                    ? List.of(reaching.region()) : List.of(), read);
        }
        Predicate<Proposition> held = toIt;
        List<ConstructionAsk.Requirement.Is> gotPast = gotPast(before.get().onEveryRun(), asks,
                ask);
        Pullback.Once<NumericDomain<NumericTerm>> relations =
                new Pullback.Once<>(() -> relationsOf(both));
        Optional<WhatAConstructionAsks> told = ask.toldOf(is -> held.test(is.read())
                || (is.exact() != null && (gotPast.stream()
                        .anyMatch(past -> past.exact().implies(is.exact()))
                        || entailedBy(relations.get(), is.exact()))));
        if (told.isEmpty()) {
            return new Judgement.Safe(one.made());
        }
        Found found = aStopAt(ask, told.get(), before.get(), both, reach.wayRead().get(), asks,
                waysTo, read, definitions);
        return switch (found) {
            case Found.AStop(Shown shown) -> new Judgement.Stops(one.made(), shown);
            case Found.None(WhyAConstructionStopIsNotShown why) -> unresolved(one, ask, told, why);
        };
    }

    /** That neither is shown of {@code one} for {@code why}, said with what it asks that the way
     *  does not hold, {@code told}: nothing of it where the way holds all of it. */
    private static Judgement unresolved(AConstructionOnTheWay one, ConstructionAsk ask,
                                        Optional<WhatAConstructionAsks> told,
                                        WhyAConstructionStopIsNotShown why) {
        return new Judgement.Unresolved(one.made(), new AConstructionStopNotShown(
                ask.construction(), ask.at(), told.map(WhatAConstructionAsks::asks), why),
                ask.bearing());
    }

    /**
     * What the relations of numbers of the input that {@code way} states leave, each number taken
     * as dense: a region holds what the way says of each number, and a relation of two, as the
     * arm of {@code if a <= b} taken the other way says of both, is held here. Taken as dense, what
     * it proves holds of every value and so of every whole one.
     */
    private static NumericDomain<NumericTerm> relationsOf(List<OnTheWay> way) {
        NumericDomain<NumericTerm> out = NumericDomain.top(NumericTerm.inOneOrder());
        for (OnTheWay entry : way) {
            if (entry instanceof OnTheWay.TakenIn(var _,
                    RowDemand.Relational(TakenConstraint.Affine affine), var _, var _)) {
                Map<NumericTerm, NumberSpace> spaces = new HashMap<>();
                affine.form().coefs().keySet()
                        .forEach(atom -> spaces.put(atom, NumberSpace.spacedOnly(Granularity.DENSE)));
                out = out.assume(affine.form(), affine.rel(), spaces);
            }
        }
        return out;
    }

    /** Whether {@code given} proves {@code asked}. */
    private static boolean entailedBy(NumericDomain<NumericTerm> given,
                                      ConstructionAsk.Requirement.OverTheInput asked) {
        return asked.form().minus(LinearForm.constant(asked.against()))
                instanceof ExactAnswer.Held<LinearForm<NumericTerm>>(var form)
                && given.entails(form, asked.rel());
    }

    /** Whether a part is held on every one of {@code ways}, which are none where no region holds
     *  the way: asked of each part once, however many times it is read. */
    private static Predicate<Proposition> heldOnEvery(List<SearchRegion> ways, InputReading read) {
        Map<Proposition, Boolean> held = new HashMap<>();
        return part -> held.computeIfAbsent(part, stated -> !ways.isEmpty()
                && ways.stream().allMatch(way -> DemandReading.heldBy(stated, read, way)));
    }

    /** What {@code judged} leave unresolved, as a finding says it, in the order judged. */
    static List<AConstructionStopNotShown> notShown(List<Judgement> judged) {
        List<AConstructionStopNotShown> out = new ArrayList<>();
        for (Judgement each : judged) {
            if (each instanceof Judgement.Unresolved(var _, AConstructionStopNotShown told,
                    var _)) {
                out.add(told);
            }
        }
        return out;
    }

    /**
     * What shows a run on the way stops at a construction, as a finding says it: what it asks and
     * the number the value of the input holds at each place, in the order the input {@code read}
     * reads declares its places. Made from what was shown here and from nothing else.
     */
    static List<AConstructionStopShown> stopsShown(List<Judgement> judged, InputReading read) {
        List<AConstructionStopShown> out = new ArrayList<>();
        for (Judgement each : judged) {
            if (each instanceof Judgement.Stops(var _, Shown shown)) {
                List<AStopShown.NumberAt> at = new ArrayList<>();
                for (Position place : read.domain().positions()) {
                    ExactRatio held = shown.at().get(new NumericTerm.ValueOf(place.path()));
                    if (held != null) {
                        at.add(new AStopShown.NumberAt(place.path(), held.floor().orNull()));
                    }
                }
                out.add(new AConstructionStopShown(shown.told(), at));
            }
        }
        return out;
    }

    /**
     * What every run that gets to {@code ask}'s construction has met by then, of what the
     * constructions among {@code asks} it has got past ask: each part of a condition that holds
     * wherever the condition does, of every construction the parts in {@code onEveryRun} work out
     * whenever they run, read over numbers of the input.
     *
     * <p>A run that got here worked each of those out and was not ended by it, and a construction
     * whose type refuses what it is handed ends the run — so it was built, and what it asks holds.
     * That rests on a step being a value a run gets past or stops at, which is what
     * {@link Evaluated#inOrder} lists: the construction an attempt tests, which takes the other arm
     * where it is refused, is the attempt's deciding and no step of it.
     *
     * <p>What those parts work out whenever they run is gathered once, and each construction among
     * {@code asks} is looked for in it, since asking it part by part of each would go down the tree
     * once for every construction and every part.
     */
    private static List<ConstructionAsk.Requirement.Is> gotPast(List<Core> onEveryRun,
                                                               List<ConstructionAsk> asks,
                                                               ConstructionAsk ask) {
        Set<Core> worked = Collections.newSetFromMap(new IdentityHashMap<>());
        onEveryRun.forEach(part -> Evaluated.runningWhenever(part, worked));
        List<ConstructionAsk.Requirement.Is> out = new ArrayList<>();
        for (ConstructionAsk other : asks) {
            if (other.made() == ask.made()) {
                continue;
            }
            if (worked.contains(other.made())) {
                other.requirement().heldWhereItIs().stream()
                        .filter(is -> is.exact() != null).forEach(out::add);
            }
        }
        return out;
    }

    /** What the proof of a stop at a construction came to: the stop, or the first thing it could
     *  not rest on. */
    private sealed interface Found {

        record AStop(Shown shown) implements Found {}

        record None(WhyAConstructionStopIsNotShown why) implements Found {}
    }

    /**
     * A construction a run may work out before the one judged, and the runs it is worked out on:
     * every run that takes the way to the one judged, or, where {@code onlyWhere} holds some
     * condition, only those of them that meet every one of those as well — the conditions of the
     * way to it that are not on the way to the one judged, as an arm it stands on puts there.
     *
     * <p>A run it is not worked out on is no run it ends, so what it asks is asked of a value only
     * where the value meets {@code onlyWhere}. Asked of every value where a condition of the way to
     * it is not read, which asks more of a value and never less.
     */
    private record Before(ConstructionAsk ask, List<TakenConstraint.Affine> onlyWhere) {

        Before {
            onlyWhere = List.copyOf(onlyWhere);
        }

        /** {@code ask}'s construction, met on {@code itsWay} — none where the walk did not meet
         *  it on one way — before one met on {@code way}. */
        static Before of(ConstructionAsk ask, List<OnTheWay> itsWay, List<OnTheWay> way) {
            if (itsWay == null) {
                return new Before(ask, List.of());
            }
            List<TakenConstraint.Affine> only = new ArrayList<>();
            for (OnTheWay entry : itsWay) {
                if (way.contains(entry)) {
                    continue;
                }
                if (entry instanceof OnTheWay.TakenIn(var _,
                        RowDemand.Relational(TakenConstraint.Affine affine), var _, var _)
                        && numbersOf(affine.form(), new LinkedHashSet<>())) {
                    only.add(affine);
                } else if (!(entry instanceof OnTheWay.Settled(var _, var _, boolean thisWay)
                        && thisWay)) {
                    return new Before(ask, List.of());
                }
            }
            return new Before(ask, only);
        }

        /** Whether a run with the input's numbers at {@code at} works it out: false only where a
         *  condition of {@code onlyWhere} is worked out exactly and does not hold there. */
        boolean workedOutAt(Map<NumericTerm, ExactRatio> at) {
            for (TakenConstraint.Affine condition : onlyWhere) {
                ExactRatio comes = valueOf(condition.form(), at);
                if (comes != null && !condition.rel().holds(comes.signum())) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * Whether a run taking {@code way}, the way to the comparison and to {@code ask}'s
     * construction, stops at the construction: everything a run may work out first is asked
     * whether it may end the run, among constructions that ask {@code asks} and are met on the
     * ways {@code waysTo} holds, the way whether it is read — every condition of it held in
     * {@code way} only where {@code wayRead} — and only where all of that is answered is a value
     * looked for. A build among what a run works out first is asked of its template
     * ({@code definitions}).
     */
    private static Found aStopAt(ConstructionAsk ask, WhatAConstructionAsks told,
                                 WhatARunWorksOutBeforeACount.BeforeAConstruction before,
                                 List<OnTheWay> way, boolean wayRead, List<ConstructionAsk> asks,
                                 Map<Core, List<OnTheWay>> waysTo, InputReading read,
                                 ValueTemplates definitions) {
        List<ConstructionAsk> passed = new ArrayList<>();
        Set<Core> through = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Core part : before.onSomeRun()) {
            if (!getsPast(part, asks, passed, definitions, through)) {
                return new Found.None(WhyAConstructionStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
            }
        }
        if (!wayRead) {
            return new Found.None(WhyAConstructionStopIsNotShown.A_CONDITION_NOT_READ);
        }
        List<TakenConstraint.Affine> taken = new ArrayList<>();
        for (OnTheWay entry : way) {
            if (entry instanceof OnTheWay.TakenIn(var _,
                    RowDemand.Relational(TakenConstraint.Affine affine), var _, var _)) {
                taken.add(affine);
            } else if (!(entry instanceof OnTheWay.Settled(var _, var _, boolean thisWay)
                    && thisWay)) {
                return new Found.None(WhyAConstructionStopIsNotShown.A_CONDITION_NOT_READ);
            }
        }
        List<Before> first = new ArrayList<>();
        for (ConstructionAsk one : passed) {
            first.add(Before.of(one, waysTo.get(one.made()), way));
        }
        List<LinearForm<NumericTerm>> forms = new ArrayList<>();
        taken.forEach(it -> forms.add(it.form()));
        for (Before one : first) {
            formsOf(one.ask().requirement(), forms);
            one.onlyWhere().forEach(it -> forms.add(it.form()));
        }
        formsOf(ask.requirement(), forms);
        Set<NumericTerm> numbers = new LinkedHashSet<>();
        for (LinearForm<NumericTerm> form : forms) {
            if (!numbersOf(form, numbers)) {
                return new Found.None(WhyAConstructionStopIsNotShown.NOT_OVER_THE_INPUT);
            }
        }
        Set<TermPath> places = new LinkedHashSet<>();
        for (NumericTerm number : numbers) {
            places.add(((NumericTerm.ValueOf) number).position());
        }
        // A value of the input holding them exists where they meet what the input's declarations
        // ask of the places, which the value looked for is asked to meet with the way.
        Optional<AValueOfTheInput.Meets> declared =
                AValueOfTheInput.whatAValueAtThemMeets(read, places);
        if (declared.isEmpty()) {
            return new Found.None(WhyAConstructionStopIsNotShown.NO_VALUE_SHOWN);
        }
        taken.addAll(declared.get().constraints());
        Map<NumericTerm, List<ExactRatio>> tried = new LinkedHashMap<>();
        for (NumericTerm number : numbers) {
            tried.put(number, valuesToTry(number, taken, first, ask, read));
        }
        int[] left = {MOST_VALUES_TRIED};
        Shown shown = tryingEach(List.copyOf(numbers), 0, new LinkedHashMap<>(), tried, left,
                values -> (stopsAt(values, taken, first, ask)
                        && declared.get().tiesHoldAt(values))
                        ? new Shown(told, values) : null);
        if (shown != null) {
            return new Found.AStop(shown);
        }
        // A part of what it asks over something that is no number of the input is met nowhere
        // the arithmetic can say, so no value is refused by it.
        return new Found.None(!ask.requirement().overTheInput()
                ? WhyAConstructionStopIsNotShown.NOT_OVER_THE_INPUT
                : left[0] <= 0 ? WhyAConstructionStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED
                : WhyAConstructionStopIsNotShown.NO_VALUE_FOUND);
    }

    /**
     * Whether working {@code e} out, and everything under it, gets a run past it, the value
     * looked for meeting what {@code passed} ask: every node of it ends no run whatever the input,
     * or is a construction among {@code asks} whose condition is read over numbers of the input,
     * which is then added to {@code passed}. The construction an attempt tests takes the other arm
     * where it is refused, and ends nothing ({@link WhatARunMayEndFor#forEachWorkedOut}).
     *
     * <p>A build of a value works its template out ({@link ValueTemplates#builtBy}), which is in
     * no tree the build stands in and {@link WhatARunMayEndFor#itself} does not answer for, so a
     * run gets past the build where it gets past every node of the template. Asked here and not of
     * {@link WhatARunMayEndFor.WithDefinitions}: what this asks of a construction is that the value
     * looked for meets what it asks, which is no ending of a run. {@code through} holds the
     * templates being gone through, so a template built inside itself, by way of others, is one a
     * run is not shown to get past: the language refuses a value that reaches itself, and the
     * templates handed here are not what holds that.
     */
    private static boolean getsPast(Core e, List<ConstructionAsk> asks,
                                    List<ConstructionAsk> passed,
                                    ValueTemplates definitions, Set<Core> through) {
        Core node = Core.withoutStanding(e);
        Core template = definitions.builtBy(node);
        if (template != null) {
            return pastTheTemplate(template, asks, passed, definitions, through);
        }
        if (node instanceof Core.IfConstructed attempt) {
            boolean[] all = {true};
            WhatARunMayEndFor.forEachWorkedOut(attempt, (part, _) -> all[0] = all[0]
                    && getsPast(part, asks, passed, definitions, through));
            return all[0];
        }
        for (Core each : Core.subexpressionsAt(node)) {
            Core built = definitions.builtBy(each);
            if (built != null) {
                if (!pastTheTemplate(built, asks, passed, definitions, through)) {
                    return false;
                }
            } else if (Core.withoutStanding(each) instanceof Core.Construct) {
                ConstructionAsk known = asks.stream().filter(ask -> ask.of(each)).findFirst()
                        .orElse(null);
                if (known == null || !known.requirement().overTheInput()) {
                    return false;
                }
                passed.add(known);
            } else if (!WhatARunMayEndFor.itself(each).endsNone()) {
                return false;
            }
        }
        boolean[] all = {true};
        Core.forEachChild(node, child -> all[0] = all[0]
                && getsPast(child, asks, passed, definitions, through));
        return all[0];
    }

    /** Whether a run gets past working {@code template} out ({@link #getsPast}): not where it
     *  is being gone through already. */
    private static boolean pastTheTemplate(Core template, List<ConstructionAsk> asks,
                                           List<ConstructionAsk> passed,
                                           ValueTemplates definitions, Set<Core> through) {
        if (!through.add(template)) {
            return false;
        }
        boolean past = getsPast(template, asks, passed, definitions, through);
        through.remove(template);
        return past;
    }

    /** Every form {@code requirement} stands on that is over numbers of the input, into
     *  {@code into}. */
    private static void formsOf(ConstructionAsk.Requirement requirement,
                                List<LinearForm<NumericTerm>> into) {
        switch (requirement) {
            case ConstructionAsk.Requirement.Always _, ConstructionAsk.Requirement.Never _ -> { }
            case ConstructionAsk.Requirement.Is is -> {
                if (is.exact() != null) {
                    into.add(is.exact().form());
                }
            }
            case ConstructionAsk.Requirement.AllOf all ->
                    all.parts().forEach(part -> formsOf(part, into));
            case ConstructionAsk.Requirement.OneOf one ->
                    one.parts().forEach(part -> formsOf(part, into));
        }
    }

    /** Whether every number {@code form} is over is a value at a place of the input, or a product
     *  of forms of such values, each added to {@code into}. */
    private static boolean numbersOf(LinearForm<NumericTerm> form, Set<NumericTerm> into) {
        for (NumericTerm term : form.coefs().keySet()) {
            switch (term) {
                case NumericTerm.ValueOf _ -> into.add(term);
                case NumericTerm.ProductOf product -> {
                    if (!numbersOf(product.one(), into) || !numbersOf(product.other(), into)) {
                        return false;
                    }
                }
                default -> {
                    return false;
                }
            }
        }
        return true;
    }

    /** Whether a condition holds at a value of the input, fails there, or the arithmetic cannot
     *  say. */
    private enum Met { HOLDS, FAILS, NOT_KNOWN }

    /**
     * Whether a run with the input's numbers at {@code at} takes {@code way}, meets what each of
     * {@code first} it works out asks, and does not meet what {@code ask} asks: each worked out
     * exactly, and none of it shown where the arithmetic cannot say.
     */
    private static boolean stopsAt(Map<NumericTerm, ExactRatio> at,
                                   List<TakenConstraint.Affine> way,
                                   List<Before> first, ConstructionAsk ask) {
        for (TakenConstraint.Affine condition : way) {
            ExactRatio comes = valueOf(condition.form(), at);
            if (comes == null || !condition.rel().holds(comes.signum())) {
                return false;
            }
        }
        for (Before one : first) {
            if (one.workedOutAt(at) && met(one.ask().requirement(), at) != Met.HOLDS) {
                return false;
            }
        }
        return met(ask.requirement(), at) == Met.FAILS;
    }

    /** Whether a value of the input with its numbers at {@code at} meets {@code requirement}. */
    private static Met met(ConstructionAsk.Requirement requirement,
                           Map<NumericTerm, ExactRatio> at) {
        return switch (requirement) {
            case ConstructionAsk.Requirement.Always _ -> Met.HOLDS;
            case ConstructionAsk.Requirement.Never _ -> Met.FAILS;
            case ConstructionAsk.Requirement.Is is -> {
                ExactRatio comes = is.exact() == null ? null : valueOf(is.exact().form(), at);
                if (comes == null) {
                    yield Met.NOT_KNOWN;
                }
                yield is.exact().rel().holds(Integer.signum(comes.compareTo(is.exact().against())))
                        ? Met.HOLDS : Met.FAILS;
            }
            case ConstructionAsk.Requirement.AllOf all -> {
                Met out = Met.HOLDS;
                for (ConstructionAsk.Requirement part : all.parts()) {
                    Met one = met(part, at);
                    if (one == Met.FAILS) {
                        yield Met.FAILS;
                    }
                    if (one == Met.NOT_KNOWN) {
                        out = Met.NOT_KNOWN;
                    }
                }
                yield out;
            }
            case ConstructionAsk.Requirement.OneOf one -> {
                Met out = Met.FAILS;
                for (ConstructionAsk.Requirement part : one.parts()) {
                    Met each = met(part, at);
                    if (each == Met.HOLDS) {
                        yield Met.HOLDS;
                    }
                    if (each == Met.NOT_KNOWN) {
                        out = Met.NOT_KNOWN;
                    }
                }
                yield out;
            }
        };
    }

    /** What {@code form} comes to with each number of the input at {@code at}, a product of two
     *  forms as the two multiplied; null where the arithmetic cannot say. */
    private static ExactRatio valueOf(LinearForm<NumericTerm> form,
                                      Map<NumericTerm, ExactRatio> at) {
        Map<NumericTerm, ExactRatio> values = new LinkedHashMap<>(at);
        for (NumericTerm term : form.coefs().keySet()) {
            if (term instanceof NumericTerm.ProductOf product) {
                ExactRatio one = valueOf(product.one(), at);
                ExactRatio other = valueOf(product.other(), at);
                if (one == null || other == null
                        || !(one.times(other) instanceof ExactAnswer.Held<ExactRatio>(
                                ExactRatio both))) {
                    return null;
                }
                values.put(term, both);
            }
        }
        return WholeValuesMeeting.valueOf(form, values);
    }

    /** What is asked of one value of every number. */
    @FunctionalInterface
    private interface Asking {
        Shown at(Map<NumericTerm, ExactRatio> values);
    }

    /** {@code ask} of each way of putting {@code numbers} from {@code from} on at the values tried
     *  for each, while {@code left} lasts, until it answers. */
    private static Shown tryingEach(List<NumericTerm> numbers, int from,
                                    Map<NumericTerm, ExactRatio> values,
                                    Map<NumericTerm, List<ExactRatio>> tried, int[] left,
                                    Asking ask) {
        if (from == numbers.size()) {
            if (left[0] <= 0) {
                return null;
            }
            left[0]--;
            return ask.at(values);
        }
        for (ExactRatio value : tried.get(numbers.get(from))) {
            values.put(numbers.get(from), value);
            Shown found = tryingEach(numbers, from + 1, values, tried, left, ask);
            if (found != null || left[0] <= 0) {
                return found;
            }
        }
        values.remove(numbers.get(from));
        return null;
    }

    /**
     * The values {@code number} is tried at: nought and one either side, the ends of its place, and
     * on both sides of where each condition over it alone turns — of the way, of what the
     * constructions before ask and of the way to them, and of what {@code ask} asks — each once,
     * and none past the ends of its place. None at which a condition of the way over it alone does not hold, which no value
     * taking the way has, so the budget is not spent on it. Those at which a part of what
     * {@code ask} asks over it alone is not met come first, so that a value taking each number to
     * the side the construction refuses is tried before the budget is spent on the others.
     */
    private static List<ExactRatio> valuesToTry(NumericTerm number,
                                                List<TakenConstraint.Affine> way,
                                                List<Before> first,
                                                ConstructionAsk ask, InputReading read) {
        Set<ExactRatio> out = new LinkedHashSet<>();
        FormRange ends = FormRange.endsOf(number, read);
        for (long each : new long[] {0, 1, -1}) {
            out.add(ExactRatio.of(each));
        }
        if (ends != null) {
            out.add(ends.least());
            out.add(ends.greatest());
        }
        for (TakenConstraint.Affine condition : way) {
            turnsAt(number, condition.form(), ExactRatio.ZERO, out);
        }
        for (Before one : first) {
            for (TakenConstraint.Affine condition : one.onlyWhere()) {
                turnsAt(number, condition.form(), ExactRatio.ZERO, out);
            }
        }
        List<ConstructionAsk.Requirement> asked = new ArrayList<>();
        first.forEach(one -> asked.add(one.ask().requirement()));
        asked.add(ask.requirement());
        for (ConstructionAsk.Requirement requirement : asked) {
            for (ConstructionAsk.Requirement.Is is : everyFormOf(requirement)) {
                if (is.exact() != null) {
                    turnsAt(number, is.exact().form(), is.exact().against(), out);
                }
            }
        }
        List<ExactRatio> within = out.stream().filter(each -> each.isWhole()
                && (ends == null || (each.compareTo(ends.least()) >= 0
                        && each.compareTo(ends.greatest()) <= 0))
                && way.stream().noneMatch(condition -> failsAlone(condition, number, each)))
                .toList();
        List<ExactRatio> refused = new ArrayList<>();
        List<ExactRatio> rest = new ArrayList<>();
        for (ExactRatio value : within) {
            boolean refusedThere = everyFormOf(ask.requirement()).stream().anyMatch(is ->
                    is.exact() != null && is.exact().form().coefs().keySet().equals(Set.of(number))
                            && met(is, Map.of(number, value)) == Met.FAILS);
            if (refusedThere) {
                refused.add(value);
            } else {
                rest.add(value);
            }
        }
        refused.addAll(rest);
        return refused;
    }

    /** Whether {@code condition}, of the way, is over {@code number} alone and does not hold where
     *  it is {@code value}. */
    private static boolean failsAlone(TakenConstraint.Affine condition, NumericTerm number,
                                      ExactRatio value) {
        if (!condition.form().coefs().keySet().equals(Set.of(number))) {
            return false;
        }
        ExactRatio comes = valueOf(condition.form(), Map.of(number, value));
        return comes != null && !condition.rel().holds(comes.signum());
    }

    /** Every form standing to a number in {@code requirement}, under every one of several and one
     *  of several alike. */
    private static List<ConstructionAsk.Requirement.Is> everyFormOf(
            ConstructionAsk.Requirement requirement) {
        return switch (requirement) {
            case ConstructionAsk.Requirement.Always _, ConstructionAsk.Requirement.Never _ ->
                    List.of();
            case ConstructionAsk.Requirement.Is is -> List.of(is);
            case ConstructionAsk.Requirement.AllOf all -> all.parts().stream()
                    .flatMap(part -> everyFormOf(part).stream()).toList();
            case ConstructionAsk.Requirement.OneOf one -> one.parts().stream()
                    .flatMap(part -> everyFormOf(part).stream()).toList();
        };
    }

    /** The whole numbers either side of where {@code form}, a form of {@code number} alone, comes
     *  to {@code against}, into {@code out}; nothing where it is of anything else. */
    private static void turnsAt(NumericTerm number, LinearForm<NumericTerm> form,
                                ExactRatio against, Set<ExactRatio> out) {
        Map<NumericTerm, ExactRatio> coefs = form.coefs();
        if (coefs.size() != 1 || !coefs.containsKey(number)
                || !(against.minus(form.constant()) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio wanting))
                || !(wanting.dividedBy(coefs.get(number)) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio turns))) {
            return;
        }
        BigInteger floor = turns.floor().orNull();
        BigInteger ceiling = turns.ceiling().orNull();
        if (floor == null || ceiling == null) {
            return;
        }
        for (BigInteger each : List.of(floor.subtract(BigInteger.ONE), floor, ceiling,
                ceiling.add(BigInteger.ONE))) {
            out.add(ExactRatio.of(each));
        }
    }
}
