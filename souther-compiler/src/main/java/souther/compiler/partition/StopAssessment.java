package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.core.Core;
import souther.compiler.inputs.AStopNotShown;
import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhyAStopIsNotShown;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Whether a run stops in each operation a comparison works out: shown not to, shown to, or
 * neither.
 *
 * <p>Three answers, each with what shows it. {@link Judgement.Safe} is a proof that no run getting
 * to the operation stops in it, and may rest on what the way leaves a number, which holds every
 * row that arrives and more. {@link Judgement.Stops} is a proof that some run does, and rests on
 * one value of the input that exists, is on the way to the operation, has nothing before it end
 * the run, and works the operation out exactly past its ends: what the way leaves may hold rows
 * that never arrive, so it is where a value is looked for and never what shows one is there.
 * {@link Judgement.Unresolved} is everything else, with why. A comparison may hold all three.
 *
 * <p>A stop is shown only where every part of that is answered whole by an owner of it, and is
 * left unresolved otherwise: a value of the input only where its types state nothing of their
 * values ({@link AValueOfTheInput}), the way only where every condition on it is a relation of
 * whole numbers of the input or settled, what comes before the comparison only where every
 * operation of what may end a run there is told ({@link ComparisonReadings.Reading#workedOutBeforeIt}),
 * and the operation only where it is worked out wherever the comparison is. It and every other
 * operation a run may work out before it, there or before the comparison, are forms of those
 * numbers, but for one every value on the way keeps within its ends: the value looked for is one
 * of those, and gets past it. Showing more moves an answer from unresolved to one of the others,
 * and changes what neither of them means.
 *
 * <p>A value shown to stop a run is held against every operation judged kept within its ends on
 * the way it is on: one it takes past them is the two answers contradicting each other, and is
 * refused, never settled by taking one of them.
 */
final class StopAssessment {

    private StopAssessment() {}

    /** How many values of the input are put to the proof of one operation before it is left
     *  unresolved: as many as a search for an assignment on the way tries of one position. */
    private static final int MOST_VALUES_TRIED =
            CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT.maximum();

    /** Why no run stops in an operation, where that is shown. */
    enum WhyNone {
        /** No row arrives where it is worked out. */
        NOT_WORKED_OUT,
        /** Every row the way leaves keeps it within its ends. */
        WITHIN_ITS_ENDS,
        /** Every row the way leaves keeps the divisor away from nought. */
        DIVISOR_AWAY_FROM_NOUGHT
    }

    /**
     * Where a run may stop in working something out: an operation whose answer may lie past the
     * ends of its type, or a quotient whose divisor may be nought. The first stops where the
     * answer is outside its ends and the second where an operand is outside what the operation is
     * defined on, so neither is said as the other.
     */
    sealed interface Site {

        /** What is worked out there, as a finding writes it. */
        String written();

        /**
         * Whether a run stopping at {@code other} stops in what this is, as a finding says it:
         * what is shown of a site is that a run stops in it as written, for its kind of stop, at
         * a value, and not at which place writing it a run stops first. A value that takes this
         * past where it stops takes such another past where it stops, or lets it by, so a run
         * with it stops in this wherever it stops first; one is not asked to get past the other.
         */
        boolean sameStopAs(Site other);

        /**
         * An operation of whole numbers, and where its answer stops being one. Another is the
         * same stop where it is written as this is and stops for the same kind of end: where its
         * type stops, or where a construction's clauses leave it.
         *
         * <p>Whatever ends each is held to: that is not the same telling
         * ({@link UndividedByARelation.IntOperation#sameOperationAs}), which is a question of what
         * was told and not of where a run stops. One with narrower ends that a value takes past
         * them stops a run in this as written before this is got to; one with wider ends lets the
         * value by to this. Two such are told of one place in a model: a date moved and read
         * again by its year is told held to the calendar's days and once more held to the days
         * of the years it counts, which end a day apart.
         */
        record PastItsEnds(UndividedByARelation.IntOperation operation) implements Site {

            @Override
            public String written() {
                return UndividedByARelation.written(operation.form());
            }

            @Override
            public boolean sameStopAs(Site other) {
                return other instanceof PastItsEnds(var that)
                        && that.form().equals(operation.form())
                        && that.ofTheRepresentation() == operation.ofTheRepresentation();
            }
        }

        /** A quotient, and where its divisor is nought ({@link AbortKind#DIVISION_BY_ZERO}).
         *  Another is the same stop where it divides by what this does. */
        record ByNought(LinearForm<NumericTerm> divisor) implements Site {

            @Override
            public String written() {
                return "division by " + UndividedByARelation.written(divisor);
            }

            @Override
            public boolean sameStopAs(Site other) {
                return other instanceof ByNought(var that) && that.equals(divisor);
            }
        }
    }

    /** What is shown of one place a run may stop, or of what a run works out where no site is
     *  told. */
    sealed interface Judgement {

        /** No run stops at {@code site}. */
        record Safe(Site site, WhyNone why) implements Judgement {}

        /** Some run stops at the site {@code shown} names. */
        record Stops(Shown shown) implements Judgement {}

        /** Neither is shown of {@code site}, or, where that is null, of a stop no site names. */
        record Unresolved(Site site, WhyAStopIsNotShown why) implements Judgement {}
    }

    /**
     * That a run stops at {@link #site}: the value of the input {@link #at}, a whole number at
     * each place it is asked of, exists, gets to the site, and works it out past its ends or with
     * its divisor at nought, as the site says. Made here and nowhere else, and only once all of
     * that is shown.
     */
    static final class Shown {

        private final Site site;
        private final Map<NumericTerm, ExactRatio> at;

        private Shown(Site site, Map<NumericTerm, ExactRatio> at) {
            this.site = site;
            this.at = Map.copyOf(at);
        }

        Site site() {
            return site;
        }

        Map<NumericTerm, ExactRatio> at() {
            return at;
        }

        @Override
        public String toString() {
            return site.written() + " at " + at;
        }
    }

    /**
     * One place a comparison works something out, as the caller that knows its ways puts it.
     *
     * @param worked      what is worked out there, and on which arm or application
     * @param aRowArrives whether a row may arrive there
     * @param way         the way to it: the way to the comparison, with what the arm or the
     *                    application states put on it where that is put on the way
     */
    record Place(ComparisonReadings.Reading.WorkedOutAt worked, boolean aRowArrives,
                 List<OnTheWay> way) {

        Place {
            way = List.copyOf(way);
        }
    }

    /**
     * What is shown of every operation a run getting to {@code each} works out at {@code places},
     * and of what it works out where no operation is told; and, where a row may arrive where the
     * statement says a run stops on rows of its own ({@code onRowsOfTheStatement}), that this is
     * unresolved.
     */
    static List<Judgement> of(ComparisonReadings.Reading each, List<Place> places,
                              boolean onRowsOfTheStatement, InputReading read) {
        return of(each, places, onRowsOfTheStatement, List.of(), read);
    }

    /**
     * Whether a run getting to {@code each} is shown to stop in something it works out at
     * {@code places} with the input meeting every one of {@code within} as well: the same showing
     * as {@link #of}, those statements put on the way of every place. What a region of the input
     * is asked of where it is to be said as far out as it can go.
     */
    static boolean aRunStopsWithin(ComparisonReadings.Reading each, List<Place> places,
                                   List<TakenConstraint.Affine> within, InputReading read) {
        return of(each, places, false, within, read).stream()
                .anyMatch(Judgement.Stops.class::isInstance);
    }

    private static List<Judgement> of(ComparisonReadings.Reading each, List<Place> places,
                                      boolean onRowsOfTheStatement,
                                      List<TakenConstraint.Affine> within, InputReading read) {
        List<Judgement> out = new ArrayList<>();
        if (onRowsOfTheStatement) {
            out.add(new Judgement.Unresolved(null, WhyAStopIsNotShown.ON_ROWS_OF_THE_STATEMENT));
        }
        List<LinearForm<NumericTerm>> divisors = divisorsOf(each, read);
        for (Place place : places) {
            UndividedByARelation.Working working = place.worked().stops().operations();
            WhatAWayLeavesOfAValue left = place.aRowArrives()
                    ? WhatAWayLeavesOfAValue.along(read, place.way()) : null;
            if (left != null && working.aStopUntold()
                    && working.leavesUntoldBeyond(each.quotients())) {
                out.add(new Judgement.Unresolved(null, WhyAStopIsNotShown.NO_OPERATION_TOLD));
            }
            List<UndividedByARelation.IntOperation> operations = working.operations();
            for (int at = 0; at < operations.size(); at++) {
                Site site = new Site.PastItsEnds(operations.get(at));
                if (left == null) {
                    out.add(new Judgement.Safe(site, WhyNone.NOT_WORKED_OUT));
                } else if (keptWithinItsEnds(left, operations.get(at))) {
                    out.add(new Judgement.Safe(site, WhyNone.WITHIN_ITS_ENDS));
                } else {
                    out.add(aStopIn(each, place, left, site, operations.get(at).origin().node(),
                            divisors, within, read));
                }
            }
        }
        out.addAll(divisionsOf(each, places, divisors, within, read));
        return out;
    }

    /** Whether every value the way {@code left} is of leaves keeps {@code operation} within its
     *  ends: no run along it stops there, the value a stop is shown at among them. */
    private static boolean keptWithinItsEnds(WhatAWayLeavesOfAValue left,
                                             UndividedByARelation.IntOperation operation) {
        return left.keepsWithinItsType(operation) || left.noRowTakesItPastItsEnds(operation);
    }

    /**
     * What each quotient evaluating the comparison always works out is divided by, as a form of
     * the value at places of the input, in the order they are worked out; null where the divisor
     * is no such form. A quotient is kept in its place whether or not its divisor is read: one
     * worked out before another that stops it is one the other is not got to past, and what is not
     * read of it is not that it does not stop.
     */
    private static List<LinearForm<NumericTerm>> divisorsOf(ComparisonReadings.Reading each,
                                                            InputReading read) {
        List<LinearForm<NumericTerm>> out = new ArrayList<>();
        for (Core.Binary quotient : each.quotients()) {
            LinearForm<NumericTerm> form = AffineReading.formOf(quotient.right(), each.reads(),
                    read, new ElementsMet(), AffineReading.Unkept.EVERY_NAME_AFRESH);
            out.add(form != null && form.coefs().keySet().stream()
                    .allMatch(NumericTerm.ValueOf.class::isInstance) ? form : null);
        }
        return out;
    }

    /**
     * Every place a run may stop at before it is past {@code site}, which {@code place} works out
     * at {@code node}, as a value looked for there is asked to get past them: one rule for each
     * kind of place, and one for which of them is the site itself.
     *
     * <p>An operation is worked out of its operands, and its node may be more than it, so it may
     * stop anywhere in what that node works out: one is passed over only where it is worked out
     * of this ({@code after}) or the whole of its node comes after this
     * ({@link EvaluationPlaces#comesAfter}). A quotient stops at its own step, past its operands,
     * so one is passed over where that step comes after all of this
     * ({@link EvaluationPlaces#isWorkedOutAfter}) — a quotient whose dividend holds this divides
     * after it. What a run works out before the comparison is before all of it. One whose place is
     * not known is asked of the value. One that is the same stop as the site
     * ({@link Site#sameStopAs}) is not: a run that stops there stops in it.
     *
     * <p>A quotient whose divisor is no form of the input's numbers is among them as null, one a
     * value is not shown to get past ({@link #aStopIn}): what is not read of it is not that it does
     * not stop.
     *
     * @param operations the operations, before the comparison and then in it
     * @param divisors   the divisor of each quotient, as {@code each} says them
     */
    private record StopsBefore(List<UndividedByARelation.IntOperation> operations,
                               List<LinearForm<NumericTerm>> divisors) {

        static StopsBefore of(ComparisonReadings.Reading each, Site site, Core node,
                              UndividedByARelation.Working earlier,
                              UndividedByARelation.Working working,
                              List<LinearForm<NumericTerm>> divisors) {
            int at = site instanceof Site.PastItsEnds(var operation)
                    ? indexOf(working.operations(), operation) : -1;
            List<UndividedByARelation.IntOperation> operations = new ArrayList<>();
            for (UndividedByARelation.IntOperation it : earlier.operations()) {
                if (!site.sameStopAs(new Site.PastItsEnds(it))) {
                    operations.add(it);
                }
            }
            for (int other = 0; other < working.operations().size(); other++) {
                UndividedByARelation.IntOperation it = working.operations().get(other);
                if (other != at && !it.after().contains(at)
                        && !each.places().comesAfter(it.origin().node(), node)
                        && !site.sameStopAs(new Site.PastItsEnds(it))) {
                    operations.add(it);
                }
            }
            List<LinearForm<NumericTerm>> before = new ArrayList<>();
            for (int quotient = 0; quotient < divisors.size(); quotient++) {
                LinearForm<NumericTerm> divisor = divisors.get(quotient);
                if (!each.places().isWorkedOutAfter(each.quotients().get(quotient), node)
                        && !(divisor != null && site.sameStopAs(new Site.ByNought(divisor)))) {
                    before.add(divisor);
                }
            }
            return new StopsBefore(operations, before);
        }
    }

    /**
     * What is shown of each quotient the comparison always works out, which a run works out
     * wherever it evaluates the comparison and stops at where the divisor is nought. None stops
     * where the way to the comparison, at each place it is worked out, keeps the divisor from
     * nought. A stop is looked for where the comparison is worked out along one way — every place
     * it is worked out at is on the way to the comparison itself, and not on an arm or an
     * application of a way of its own — what is worked out there is all told, and the quotients
     * before it have a divisor that is a form of the input's numbers and is not nought.
     */
    private static List<Judgement> divisionsOf(ComparisonReadings.Reading each,
                                               List<Place> places,
                                               List<LinearForm<NumericTerm>> divisors,
                                               List<TakenConstraint.Affine> within,
                                               InputReading read) {
        List<Judgement> out = new ArrayList<>();
        Place beside = new Place(new ComparisonReadings.Reading.WorkedOutAt(
                StopEvidence.ofWhatIsToldOf(UndividedByARelation.Working.NO_STOPS), null, null),
                true, each.assumed());
        List<Place> comparison = places.isEmpty() ? List.of(beside) : places;
        for (int at = 0; at < divisors.size(); at++) {
            LinearForm<NumericTerm> divisor = divisors.get(at);
            // A divisor that is no form of places of the input — a choice, a count or a total of
            // a container — is the stop of the owner of that quotient, which holds the rows to
            // where it answers ({@link QuotientByAValue.Read#answers}) and says what it says of
            // the rest: none is judged here, and none after it is shown past it.
            if (divisor == null) {
                continue;
            }
            Site site = new Site.ByNought(divisor);
            Core node = each.quotients().get(at);
            // Wherever the comparison is worked out, along the way to it there.
            if (comparison.stream().allMatch(place -> {
                WhatAWayLeavesOfAValue left = place.aRowArrives()
                        ? WhatAWayLeavesOfAValue.along(read, place.way()) : null;
                return left == null || left.keepsAwayFromNought(divisor);
            })) {
                out.add(new Judgement.Safe(site, WhyNone.DIVISOR_AWAY_FROM_NOUGHT));
            } else if (places.stream().map(Place::way).distinct().count() > 1) {
                out.add(new Judgement.Unresolved(site, WhyAStopIsNotShown.NOT_EVERY_OPERATION_TOLD));
            } else {
                Place there = comparison.getFirst();
                out.add(aStopIn(each, there, WhatAWayLeavesOfAValue.along(read, there.way()), site,
                        node, divisors, within, read));
            }
        }
        return out;
    }

    /** Whether some quotient the comparison always works out may have its divisor at nought: a run
     *  is shown to stop there, or is not shown not to. What the rows that get past it leave of
     *  the numbers says nothing of the divisor at nought. */
    static boolean mayDivideByNought(List<Judgement> judged) {
        return judged.stream().anyMatch(each -> each instanceof Judgement.Stops(Shown shown)
                ? shown.site() instanceof Site.ByNought
                : each instanceof Judgement.Unresolved(var site, var _)
                        && site instanceof Site.ByNought);
    }

    /**
     * What shows a run stops in what {@code judged} are of, as a finding says it: each stop shown,
     * its operation as written and the number the value of the input holds at each place, in the
     * order the input {@code read} reads declares its places. Made from what was shown here and
     * from nothing else, so a finding that a run stops is said only where this compiler has shown
     * one does.
     */
    static List<AStopShown> stopsShown(List<Judgement> judged, InputReading read) {
        List<AStopShown> out = new ArrayList<>();
        for (Judgement each : judged) {
            if (each instanceof Judgement.Stops(Shown shown)) {
                List<AStopShown.NumberAt> at = new ArrayList<>();
                for (Position place : read.domain().positions()) {
                    ExactRatio held = shown.at().get(new NumericTerm.ValueOf(place.path()));
                    if (held != null) {
                        at.add(new AStopShown.NumberAt(place.path(), held.floor().orNull()));
                    }
                }
                out.add(new AStopShown(shown.site().written(), at));
            }
        }
        return out;
    }

    /** Each operation {@code judged} leave unresolved, as written, and why, in the order they were
     *  judged: none written where no operation names the stop. */
    static List<AStopNotShown> stopsNotShown(List<Judgement> judged) {
        List<AStopNotShown> out = new ArrayList<>();
        for (Judgement each : judged) {
            if (each instanceof Judgement.Unresolved(var site, WhyAStopIsNotShown why)) {
                out.add(new AStopNotShown(Optional.ofNullable(site).map(Site::written), why));
            }
        }
        return out;
    }

    /**
     * That a run stops at {@code site}, one of what {@code place} works out, or why that is not
     * shown. Where it is worked out, how the way gets there and what is worked out before it are
     * asked first, and a value is looked for only where all of them are answered. The value
     * meets {@code within} as it meets the way, which {@code left} is what is left of.
     */
    private static Judgement aStopIn(ComparisonReadings.Reading each, Place place,
                                     WhatAWayLeavesOfAValue left, Site site, Core siteNode,
                                     List<LinearForm<NumericTerm>> divisors,
                                     List<TakenConstraint.Affine> within, InputReading read) {
        UndividedByARelation.Working working = place.worked().stops().operations();
        // On an arm or an application, a run gets there only where taking the arm or making the
        // application holds, which is on the way only where the comparison is stated as a
        // condition: then the value tried is asked to meet it with the rest of the way.
        if (each.statedAsACondition().isEmpty()) {
            if (place.worked().madeWhere() != null) {
                return new Judgement.Unresolved(site, WhyAStopIsNotShown.ON_AN_APPLICATION);
            }
            if (place.worked().onAnArm() != null) {
                return new Judgement.Unresolved(site, WhyAStopIsNotShown.ON_AN_ARM);
            }
        }
        // A working is not on every run where the expression the comparison was stopped at may
        // end a run before the operations it tells. A quotient is worked out wherever the
        // comparison is ({@link QuotientsEveryRunWorksOut}), so only an operation is asked of the
        // rest being worked out on every run. The stop of a quotient that is among those asked
        // is not left untold: a witness is asked to get past it.
        if (working.leavesUntoldBeyond(each.quotients())
                || (site instanceof Site.PastItsEnds && !working.onEveryRun())) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.NOT_EVERY_OPERATION_TOLD);
        }
        Optional<UndividedByARelation.Working> earlier = each.workedOutBeforeIt();
        if (earlier.isEmpty()) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        }
        List<TakenConstraint.Affine> way = new ArrayList<>();
        for (OnTheWay entry : place.way()) {
            if (entry instanceof OnTheWay.TakenIn(var _,
                    RowDemand.Relational(TakenConstraint.Affine affine), var _, var _)) {
                way.add(affine);
            } else if (entry instanceof OnTheWay.Narrowed narrowed
                    && aPlaceOnItsOrder(narrowed) instanceof List<TakenConstraint.Affine> holes) {
                way.addAll(holes);
            } else if (!(entry instanceof OnTheWay.Settled(var _, var _, boolean thisWay)
                    && thisWay)) {
                return new Judgement.Unresolved(site, WhyAStopIsNotShown.A_CONDITION_NOT_READ);
            }
        }
        way.addAll(within);
        // Everything else a run may stop at before this ({@link StopsBefore}).
        StopsBefore stopsBefore = StopsBefore.of(each, site, siteNode, earlier.get(), working,
                divisors);
        List<UndividedByARelation.IntOperation> others = new ArrayList<>(stopsBefore.operations());
        List<LinearForm<NumericTerm>> quotients = stopsBefore.divisors();
        // One every value on the way keeps within its ends is got past by the value looked for,
        // which is one of them, and is not asked of it. That it is got past is held against the
        // value once one is found.
        List<UndividedByARelation.IntOperation> kept = others.stream()
                .filter(it -> keptWithinItsEnds(left, it)).toList();
        others.removeAll(kept);
        Set<NumericTerm> numbers = new LinkedHashSet<>();
        List<LinearForm<NumericTerm>> forms = new ArrayList<>();
        forms.add(switch (site) {
            case Site.PastItsEnds(var operation) -> operation.overTheInput();
            case Site.ByNought(var divisor) -> divisor;
        });
        others.forEach(it -> forms.add(it.overTheInput()));
        forms.addAll(quotients);
        way.forEach(it -> forms.add(it.form()));
        Set<TermPath> places = new LinkedHashSet<>();
        for (LinearForm<NumericTerm> one : forms) {
            if (one == null) {
                return new Judgement.Unresolved(site, WhyAStopIsNotShown.NOT_OVER_THE_INPUT);
            }
            for (NumericTerm term : one.coefs().keySet()) {
                if (!(term instanceof NumericTerm.ValueOf(TermPath position))) {
                    return new Judgement.Unresolved(site, WhyAStopIsNotShown.NOT_OVER_THE_INPUT);
                }
                numbers.add(term);
                places.add(position);
            }
        }
        // A value of the input holding them exists where they meet what the input's declarations
        // ask of the places, which the value looked for is asked to meet with the way.
        Optional<List<TakenConstraint.Affine>> declared =
                AValueOfTheInput.whatAValueAtThemMeets(read, places);
        // Where they do not, because the declarations tie the places, each value found is asked
        // whether a value of the input holds it, and nothing is looked for where no value of the
        // input is shown to exist beside the places.
        if (declared.isEmpty()) {
            if (!AValueOfTheInput.canShowHolding(read, places)) {
                return new Judgement.Unresolved(site, WhyAStopIsNotShown.NO_VALUE_SHOWN);
            }
        } else {
            way.addAll(declared.get());
        }
        int[] tries = {MOST_VALUES_TRIED};
        Before before = new Before(others, quotients, way, declared.isEmpty() ? read : null);
        Shown shown = aValueItStopsAt(site, before, List.copyOf(numbers), read, tries);
        if (shown != null) {
            return new Judgement.Stops(againstWhatIsKept(shown, kept));
        }
        // Where the values ran out with the figure, more may be left untried, and that is said.
        return new Judgement.Unresolved(site, tries[0] <= 0
                ? WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED
                : WhyAStopIsNotShown.NO_VALUE_FOUND);
    }

    /**
     * {@code shown}, held against {@code kept}, the operations judged to be kept within their ends
     * by every value on the way it is one of: each that the value works out comes out within them.
     * One that does not is the two judgements contradicting each other, which no answer here may
     * stand on, and is refused rather than one of them being taken.
     */
    private static Shown againstWhatIsKept(Shown shown,
                                           List<UndividedByARelation.IntOperation> kept) {
        for (UndividedByARelation.IntOperation each : kept) {
            ExactRatio comes = each.overTheInput() == null ? null
                    : WholeValuesMeeting.valueOf(each.overTheInput(), shown.at());
            if (comes != null && !withinItsEnds(comes, each)) {
                throw new IllegalStateException("a value shown to stop a run, " + shown
                        + ", takes " + each.form() + ", judged kept within its ends on the way,"
                        + " past them");
            }
        }
        return shown;
    }

    /**
     * A narrowing of a position to some of its cases, as what a value of it has to meet: where it
     * stands on its order is none of the places the narrowing leaves out, each a statement that
     * it is not there. Null where that is not all the narrowing asks — it asks of what a case
     * holds — or where the position is on no order, so that no place is left out.
     */
    private static List<TakenConstraint.Affine> aPlaceOnItsOrder(OnTheWay.Narrowed narrowed) {
        if (!narrowed.crossings().isEmpty() || narrowed.onItsOrder().isEmpty()) {
            return null;
        }
        List<TakenConstraint.Affine> out = new ArrayList<>();
        for (TakenConstraint.AwayFrom hole : narrowed.onItsOrder()) {
            if (!(hole.at() instanceof Count count)) {
                return null;
            }
            out.add(new TakenConstraint.Affine(new LinearForm<>(count.exactly().negated(),
                    Map.of(hole.term(), ExactRatio.ONE)), Rel.NE));
        }
        return out;
    }

    /** Where {@code operation} is among {@code operations}, by the object it is. */
    private static int indexOf(List<UndividedByARelation.IntOperation> operations,
                               UndividedByARelation.IntOperation operation) {
        for (int at = 0; at < operations.size(); at++) {
            if (operations.get(at) == operation) {
                return at;
            }
        }
        throw new IllegalArgumentException("an operation judged is one the working tells");
    }

    /**
     * What a run that stops at a site has got past before it: the conditions of the way, every
     * operation within its ends and every quotient with its divisor away from nought.
     *
     * @param held the input, where its declarations tie the places the numbers are of, so that a
     *             value found is one only where a value of the input holds it; otherwise null,
     *             the way saying what the declarations leave each place
     */
    private record Before(List<UndividedByARelation.IntOperation> operations,
                          List<LinearForm<NumericTerm>> divisors,
                          List<TakenConstraint.Affine> way, InputReading held) {}

    /**
     * A value of the input's {@code numbers} on the way, getting past what is worked out
     * {@code before} and stopping at {@code site}, or null where none of those tried does. Each
     * number but one is tried at a few values — nought and one either side, the ends of its place,
     * and on both sides of where a condition on the way of it alone turns — and the one left is
     * put where it takes the operation just past an end, or the divisor to nought. Each value
     * tried spends one of {@code left}, and none is tried once it is spent.
     */
    private static Shown aValueItStopsAt(Site site, Before before, List<NumericTerm> numbers,
                                         InputReading read, int[] left) {
        LinearForm<NumericTerm> form = switch (site) {
            case Site.PastItsEnds(var operation) -> operation.overTheInput();
            case Site.ByNought(var divisor) -> divisor;
        };
        List<TakenConstraint.Affine> way = before.way();
        Map<NumericTerm, List<ExactRatio>> tried = new LinkedHashMap<>();
        for (NumericTerm number : numbers) {
            tried.put(number, valuesToTry(number, way, read));
        }
        // A form of no number comes to its constant whatever the input holds: what is looked for
        // is a value on the way.
        if (form.coefs().isEmpty()) {
            return tryingEach(numbers, 0, new LinkedHashMap<>(), tried, left,
                    values -> stopsAt(site, before, values) ? new Shown(site, values) : null);
        }
        for (boolean above : new boolean[] {true, false}) {
            BigInteger past = switch (site) {
                case Site.PastItsEnds(var operation) -> above
                        ? operation.greatest().add(BigInteger.ONE)
                        : operation.least().subtract(BigInteger.ONE);
                case Site.ByNought _ -> BigInteger.ZERO;
            };
            for (NumericTerm free : form.coefs().keySet()) {
                List<NumericTerm> rest = numbers.stream().filter(each -> !each.equals(free))
                        .toList();
                Shown found = tryingEach(rest, 0, new LinkedHashMap<>(), tried, left, values -> {
                    ExactRatio put = whereItTakes(form, free, past, above, values);
                    FormRange ends = FormRange.endsOf(free, read);
                    if (put == null || ends == null || !within(put, ends)) {
                        return null;
                    }
                    Map<NumericTerm, ExactRatio> at = new LinkedHashMap<>(values);
                    at.put(free, put);
                    return stopsAt(site, before, at) ? new Shown(site, at) : null;
                });
                if (found != null || left[0] <= 0) {
                    return found;
                }
            }
        }
        return null;
    }

    /** What is asked of one value of every number but one. */
    @FunctionalInterface
    private interface Asking {
        Shown at(Map<NumericTerm, ExactRatio> values);
    }

    /** {@code ask} of each way of putting {@code rest} from {@code from} on at the values tried
     *  for each, while {@code left} lasts, until it answers. */
    private static Shown tryingEach(List<NumericTerm> rest, int from,
                                    Map<NumericTerm, ExactRatio> values,
                                    Map<NumericTerm, List<ExactRatio>> tried, int[] left,
                                    Asking ask) {
        if (from == rest.size()) {
            if (left[0] <= 0) {
                return null;
            }
            left[0]--;
            return ask.at(values);
        }
        for (ExactRatio value : tried.get(rest.get(from))) {
            values.put(rest.get(from), value);
            Shown found = tryingEach(rest, from + 1, values, tried, left, ask);
            if (found != null || left[0] <= 0) {
                return found;
            }
        }
        values.remove(rest.get(from));
        return null;
    }

    /**
     * The whole number {@code free} is put at for {@code form} to come to {@code past} or beyond
     * it, upwards where {@code above} and downwards otherwise, with every other number it is of at
     * {@code values}; null where the arithmetic cannot say.
     */
    private static ExactRatio whereItTakes(LinearForm<NumericTerm> form, NumericTerm free,
                                           BigInteger past, boolean above,
                                           Map<NumericTerm, ExactRatio> values) {
        Map<NumericTerm, ExactRatio> rest = new LinkedHashMap<>(form.coefs());
        ExactRatio weight = rest.remove(free);
        ExactRatio besides = WholeValuesMeeting.valueOf(new LinearForm<>(form.constant(), rest),
                values);
        if (besides == null
                || !(ExactRatio.of(past).minus(besides) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio wanting))
                || !(wanting.dividedBy(weight) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio at))) {
            return null;
        }
        BigInteger whole = (above == (weight.signum() > 0) ? at.ceiling() : at.floor()).orNull();
        return whole == null ? null : ExactRatio.of(whole);
    }

    /**
     * Whether a run with the input's numbers at {@code at} gets past what is worked out
     * {@code before}, every condition of the way, every operation within its ends and every
     * divisor not nought, and stops at {@code site}: each worked out exactly, and none of it shown
     * where the arithmetic cannot say.
     */
    private static boolean stopsAt(Site site, Before before, Map<NumericTerm, ExactRatio> at) {
        for (TakenConstraint.Affine condition : before.way()) {
            if (!WholeValuesMeeting.holdsAt(condition, at)) {
                return false;
            }
        }
        for (UndividedByARelation.IntOperation other : before.operations()) {
            ExactRatio comes = WholeValuesMeeting.valueOf(other.overTheInput(), at);
            if (comes == null || !withinItsEnds(comes, other)) {
                return false;
            }
        }
        for (LinearForm<NumericTerm> other : before.divisors()) {
            ExactRatio divisor = WholeValuesMeeting.valueOf(other, at);
            if (divisor == null || divisor.signum() == 0) {
                return false;
            }
        }
        boolean stops = switch (site) {
            case Site.PastItsEnds(var operation) -> {
                ExactRatio comes = WholeValuesMeeting.valueOf(operation.overTheInput(), at);
                yield comes != null && !withinItsEnds(comes, operation);
            }
            case Site.ByNought(var divisor) -> {
                ExactRatio comes = WholeValuesMeeting.valueOf(divisor, at);
                yield comes != null && comes.signum() == 0;
            }
        };
        return stops && (before.held() == null || AValueOfTheInput.holdingNumbers(before.held(), at));
    }

    private static boolean withinItsEnds(ExactRatio value,
                                         UndividedByARelation.IntOperation operation) {
        return value.compareTo(ExactRatio.of(operation.least())) >= 0
                && value.compareTo(ExactRatio.of(operation.greatest())) <= 0;
    }

    private static boolean within(ExactRatio value, FormRange ends) {
        return value.isWhole()
                && (ends.least() == null || value.compareTo(ends.least()) >= 0)
                && (ends.greatest() == null || value.compareTo(ends.greatest()) <= 0);
    }

    /**
     * The values {@code number} is tried at: nought and one either side, the ends of its place, and
     * on both sides of where each condition of {@code way} over it alone turns — each once, and
     * none past the ends of its place.
     */
    private static List<ExactRatio> valuesToTry(NumericTerm number,
                                                List<TakenConstraint.Affine> way,
                                                InputReading read) {
        Set<ExactRatio> out = new LinkedHashSet<>();
        FormRange ends = FormRange.endsOf(number, read);
        for (long each : new long[] {0, 1, -1}) {
            out.add(ExactRatio.of(each));
        }
        if (ends != null) {
            if (ends.least() != null) {
                out.add(ends.least());
            }
            if (ends.greatest() != null) {
                out.add(ends.greatest());
            }
        }
        for (TakenConstraint.Affine condition : way) {
            Map<NumericTerm, ExactRatio> coefs = condition.form().coefs();
            if (coefs.size() != 1 || !coefs.containsKey(number)
                    || !(condition.form().constant().negated()
                            .dividedBy(coefs.get(number))
                            instanceof ExactAnswer.Held<ExactRatio>(ExactRatio turns))) {
                continue;
            }
            BigInteger floor = turns.floor().orNull();
            BigInteger ceiling = turns.ceiling().orNull();
            if (floor == null || ceiling == null) {
                continue;
            }
            for (BigInteger each : List.of(floor.subtract(BigInteger.ONE), floor, ceiling,
                    ceiling.add(BigInteger.ONE))) {
                out.add(ExactRatio.of(each));
            }
        }
        return out.stream().filter(each -> ends == null || within(each, ends)).toList();
    }
}
