package souther.compiler.partition;

import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhyAStopIsNotShown;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
 * whole numbers of the input or settled, what comes before the comparison only where none of it
 * ends a run whatever the input ({@link ComparisonReadings.Reading#nothingBeforeItEndsARun}), and
 * the operation only where it is worked out wherever the comparison is, and it and every other
 * operation the comparison may work out before it are forms of those numbers. Showing more moves an
 * answer from unresolved to one of the others, and changes what neither of them means.
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
        WITHIN_ITS_ENDS
    }

    /** What is shown of one operation, or of what a run works out where no operation is told. */
    sealed interface Judgement {

        /** No run stops in {@code operation}. */
        record Safe(UndividedByARelation.IntOperation operation, WhyNone why)
                implements Judgement {}

        /** Some run stops in the operation {@code shown} names. */
        record Stops(Shown shown) implements Judgement {}

        /** Neither is shown of {@code operation}, or, where that is null, of a stop no operation
         *  names. */
        record Unresolved(UndividedByARelation.IntOperation operation, WhyAStopIsNotShown why)
                implements Judgement {}
    }

    /**
     * That a run stops in {@link #operation}: the value of the input {@link #at}, a whole number at
     * each place it is asked of, exists, gets to the operation and works it out past its ends.
     * Made here and nowhere else, and only once all of that is shown.
     */
    static final class Shown {

        private final UndividedByARelation.IntOperation operation;
        private final Map<NumericTerm, ExactRatio> at;

        private Shown(UndividedByARelation.IntOperation operation,
                      Map<NumericTerm, ExactRatio> at) {
            this.operation = operation;
            this.at = Map.copyOf(at);
        }

        UndividedByARelation.IntOperation operation() {
            return operation;
        }

        Map<NumericTerm, ExactRatio> at() {
            return at;
        }

        @Override
        public String toString() {
            return operation.form() + " at " + at;
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
        List<Judgement> out = new ArrayList<>();
        if (onRowsOfTheStatement) {
            out.add(new Judgement.Unresolved(null, WhyAStopIsNotShown.ON_ROWS_OF_THE_STATEMENT));
        }
        for (Place place : places) {
            UndividedByARelation.Working working = place.worked().stops().operations();
            WhatAWayLeavesOfAValue left = place.aRowArrives()
                    ? WhatAWayLeavesOfAValue.along(read, place.way()) : null;
            if (left != null && working.aStopUntold()) {
                out.add(new Judgement.Unresolved(null, WhyAStopIsNotShown.NO_OPERATION_TOLD));
            }
            List<UndividedByARelation.IntOperation> operations = working.operations();
            for (int at = 0; at < operations.size(); at++) {
                UndividedByARelation.IntOperation operation = operations.get(at);
                if (left == null) {
                    out.add(new Judgement.Safe(operation, WhyNone.NOT_WORKED_OUT));
                } else if (left.keepsWithinItsType(operation)
                        || left.noRowTakesItPastItsEnds(operation)) {
                    out.add(new Judgement.Safe(operation, WhyNone.WITHIN_ITS_ENDS));
                } else {
                    out.add(aStopIn(each, place, at, read));
                }
            }
        }
        return out;
    }

    /** Whether some run is shown to stop in what {@code judged} are of. */
    static boolean aRunStops(List<Judgement> judged) {
        return judged.stream().anyMatch(Judgement.Stops.class::isInstance);
    }

    /** Whether neither is shown of something {@code judged} are of. */
    static boolean somethingUnresolved(List<Judgement> judged) {
        return judged.stream().anyMatch(Judgement.Unresolved.class::isInstance);
    }

    /** Why neither is shown of what {@code judged} leave unresolved, each once; none where they
     *  leave nothing so. */
    static Set<WhyAStopIsNotShown> whyNotShown(List<Judgement> judged) {
        Set<WhyAStopIsNotShown> out = new LinkedHashSet<>();
        for (Judgement each : judged) {
            if (each instanceof Judgement.Unresolved(var _, WhyAStopIsNotShown why)) {
                out.add(why);
            }
        }
        return out;
    }

    /**
     * That a run stops in the operation at {@code at} of what {@code place} works out, or why that
     * is not shown. Where it is worked out, how the way gets there and what is worked out before it
     * are asked first, and a value is looked for only where all of them are answered.
     */
    private static Judgement aStopIn(ComparisonReadings.Reading each, Place place, int at,
                                     InputReading read) {
        UndividedByARelation.Working working = place.worked().stops().operations();
        UndividedByARelation.IntOperation operation = working.operations().get(at);
        if (place.worked().madeWhere() != null) {
            return new Judgement.Unresolved(operation, WhyAStopIsNotShown.ON_AN_APPLICATION);
        }
        if (place.worked().onAnArm() != null) {
            return new Judgement.Unresolved(operation, WhyAStopIsNotShown.ON_AN_ARM);
        }
        if (!working.exact() || working.aStopUntold() || !working.onEveryRun()) {
            return new Judgement.Unresolved(operation, WhyAStopIsNotShown.NOT_EVERY_OPERATION_TOLD);
        }
        if (!each.nothingBeforeItEndsARun()) {
            return new Judgement.Unresolved(operation,
                    WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        }
        List<TakenConstraint.Affine> way = new ArrayList<>();
        for (OnTheWay entry : place.way()) {
            if (entry instanceof OnTheWay.TakenIn(var _,
                    RowDemand.Relational(TakenConstraint.Affine affine), var _, var _)) {
                way.add(affine);
            } else if (!(entry instanceof OnTheWay.Settled(var _, var _, boolean thisWay)
                    && thisWay)) {
                return new Judgement.Unresolved(operation, WhyAStopIsNotShown.A_CONDITION_NOT_READ);
            }
        }
        LinearForm<NumericTerm> form = operation.overTheInput();
        // Every other operation a run may work out before this one: those this one is not worked
        // out before. One worked out of this one comes after it, and is not got to where it stops.
        List<UndividedByARelation.IntOperation> others = new ArrayList<>();
        for (int other = 0; other < working.operations().size(); other++) {
            UndividedByARelation.IntOperation it = working.operations().get(other);
            if (other != at && !it.after().contains(at)) {
                others.add(it);
            }
        }
        Set<NumericTerm> numbers = new LinkedHashSet<>();
        List<LinearForm<NumericTerm>> forms = new ArrayList<>();
        forms.add(form);
        others.forEach(it -> forms.add(it.overTheInput()));
        way.forEach(it -> forms.add(it.form()));
        Set<TermPath> places = new LinkedHashSet<>();
        for (LinearForm<NumericTerm> one : forms) {
            if (one == null) {
                return new Judgement.Unresolved(operation, WhyAStopIsNotShown.NOT_OVER_THE_INPUT);
            }
            for (NumericTerm term : one.coefs().keySet()) {
                if (!(term instanceof NumericTerm.ValueOf(TermPath position))) {
                    return new Judgement.Unresolved(operation, WhyAStopIsNotShown.NOT_OVER_THE_INPUT);
                }
                numbers.add(term);
                places.add(position);
            }
        }
        if (!AValueOfTheInput.holdsAnyWholeNumbersAt(read, places)) {
            return new Judgement.Unresolved(operation, WhyAStopIsNotShown.NO_VALUE_SHOWN);
        }
        int[] left = {MOST_VALUES_TRIED};
        Shown shown = aValueItStopsAt(operation, others, way, List.copyOf(numbers), read, left);
        if (shown != null) {
            return new Judgement.Stops(shown);
        }
        // Where the values ran out with the figure, more may be left untried, and that is said.
        return new Judgement.Unresolved(operation, left[0] <= 0
                ? WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED
                : WhyAStopIsNotShown.NO_VALUE_FOUND);
    }

    /**
     * A value of the input's {@code numbers} on the way, keeping {@code others} within their ends
     * and taking {@code operation} past one of its own, or null where none of those tried is. Each
     * number but one is tried at a few values — nought and one either side, the ends of its place,
     * and on both sides of where a condition on the way of it alone turns — and the one left is
     * put where it takes the operation just past an end. Each value tried spends one of
     * {@code left}, and none is tried once it is spent.
     */
    private static Shown aValueItStopsAt(UndividedByARelation.IntOperation operation,
                                         List<UndividedByARelation.IntOperation> others,
                                         List<TakenConstraint.Affine> way,
                                         List<NumericTerm> numbers, InputReading read,
                                         int[] left) {
        LinearForm<NumericTerm> form = operation.overTheInput();
        Map<NumericTerm, List<ExactRatio>> tried = new LinkedHashMap<>();
        for (NumericTerm number : numbers) {
            tried.put(number, valuesToTry(number, way, read));
        }
        // A form of no number comes to its constant whatever the input holds: what is looked for
        // is a value on the way.
        if (form.coefs().isEmpty()) {
            return tryingEach(numbers, 0, new LinkedHashMap<>(), tried, left,
                    values -> stopsAt(operation, others, way, values)
                            ? new Shown(operation, values) : null);
        }
        for (boolean above : new boolean[] {true, false}) {
            BigInteger past = above ? operation.greatest().add(BigInteger.ONE)
                    : operation.least().subtract(BigInteger.ONE);
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
                    return stopsAt(operation, others, way, at) ? new Shown(operation, at) : null;
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
     * Whether a run with the input's numbers at {@code at} gets past every condition of
     * {@code way}, works every one of {@code others} out within its ends, and works
     * {@code operation} out past one of its own: each worked out exactly, and none of it shown
     * where the arithmetic cannot say.
     */
    private static boolean stopsAt(UndividedByARelation.IntOperation operation,
                                   List<UndividedByARelation.IntOperation> others,
                                   List<TakenConstraint.Affine> way,
                                   Map<NumericTerm, ExactRatio> at) {
        for (TakenConstraint.Affine condition : way) {
            if (!WholeValuesMeeting.holdsAt(condition, at)) {
                return false;
            }
        }
        for (UndividedByARelation.IntOperation other : others) {
            ExactRatio comes = WholeValuesMeeting.valueOf(other.overTheInput(), at);
            if (comes == null || !withinItsEnds(comes, other)) {
                return false;
            }
        }
        ExactRatio comes = WholeValuesMeeting.valueOf(operation.overTheInput(), at);
        return comes != null && !withinItsEnds(comes, operation);
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
