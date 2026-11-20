package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.inputs.AStopNotShown;
import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
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

        /** An operation of whole numbers, and where its answer stops being one. */
        record PastItsEnds(UndividedByARelation.IntOperation operation) implements Site {

            @Override
            public String written() {
                return UndividedByARelation.written(operation.form());
            }
        }

        /** A quotient, and where its divisor is nought ({@link AbortKind#DIVISION_BY_ZERO}). */
        record ByNought(UndividedByARelation.Division division) implements Site {

            @Override
            public String written() {
                return "division by " + UndividedByARelation.written(division.divisor());
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
                Site site = new Site.PastItsEnds(operations.get(at));
                if (left == null) {
                    out.add(new Judgement.Safe(site, WhyNone.NOT_WORKED_OUT));
                } else if (left.keepsWithinItsType(operations.get(at))
                        || left.noRowTakesItPastItsEnds(operations.get(at))) {
                    out.add(new Judgement.Safe(site, WhyNone.WITHIN_ITS_ENDS));
                } else {
                    out.add(aStopIn(each, place, site, read));
                }
            }
            for (UndividedByARelation.Division division : working.divisions()) {
                Site site = new Site.ByNought(division);
                if (left == null) {
                    out.add(new Judgement.Safe(site, WhyNone.NOT_WORKED_OUT));
                } else if (left.keepsAwayFromNought(division.divisor())) {
                    out.add(new Judgement.Safe(site, WhyNone.DIVISOR_AWAY_FROM_NOUGHT));
                } else {
                    out.add(aStopIn(each, place, site, read));
                }
            }
        }
        return out;
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
     * asked first, and a value is looked for only where all of them are answered.
     */
    private static Judgement aStopIn(ComparisonReadings.Reading each, Place place, Site site,
                                     InputReading read) {
        UndividedByARelation.Working working = place.worked().stops().operations();
        if (place.worked().madeWhere() != null) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.ON_AN_APPLICATION);
        }
        if (place.worked().onAnArm() != null) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.ON_AN_ARM);
        }
        // A working is not on every run where the expression the comparison was stopped at may
        // end a run before the operations it tells. A quotient is that expression or lies in it,
        // is worked out wherever the comparison is, and is asked of what is worked out before it
        // below, so only an operation is asked of the rest being worked out on every run.
        if (!working.exact() || working.aStopUntold()
                || (site instanceof Site.PastItsEnds && !working.onEveryRun())) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.NOT_EVERY_OPERATION_TOLD);
        }
        if (!each.nothingBeforeItEndsARun()) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        }
        List<TakenConstraint.Affine> way = new ArrayList<>();
        for (OnTheWay entry : place.way()) {
            if (entry instanceof OnTheWay.TakenIn(var _,
                    RowDemand.Relational(TakenConstraint.Affine affine), var _, var _)) {
                way.add(affine);
            } else if (!(entry instanceof OnTheWay.Settled(var _, var _, boolean thisWay)
                    && thisWay)) {
                return new Judgement.Unresolved(site, WhyAStopIsNotShown.A_CONDITION_NOT_READ);
            }
        }
        // Everything else a run may work out before this: what this is not worked out before.
        // One worked out of this comes after it, and is not got to where it stops. Where this is a
        // quotient, what is worked out after it is not told, so every operation is asked.
        int at = site instanceof Site.PastItsEnds(var operation)
                ? indexOf(working.operations(), operation) : -1;
        List<UndividedByARelation.IntOperation> others = new ArrayList<>();
        for (int other = 0; other < working.operations().size(); other++) {
            UndividedByARelation.IntOperation it = working.operations().get(other);
            if (other != at && !it.after().contains(at)) {
                others.add(it);
            }
        }
        List<UndividedByARelation.Division> dividing = new ArrayList<>();
        for (UndividedByARelation.Division it : working.divisions()) {
            if (!(site instanceof Site.ByNought(var division) && division == it)
                    && !it.after().contains(at)) {
                dividing.add(it);
            }
        }
        Set<NumericTerm> numbers = new LinkedHashSet<>();
        List<LinearForm<NumericTerm>> forms = new ArrayList<>();
        forms.add(switch (site) {
            case Site.PastItsEnds(var operation) -> operation.overTheInput();
            case Site.ByNought(var division) -> division.divisor();
        });
        others.forEach(it -> forms.add(it.overTheInput()));
        dividing.forEach(it -> forms.add(it.divisor()));
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
        if (!AValueOfTheInput.holdsAnyWholeNumbersAt(read, places)) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.NO_VALUE_SHOWN);
        }
        int[] left = {MOST_VALUES_TRIED};
        Before before = new Before(others, dividing, way);
        Shown shown = aValueItStopsAt(site, before, List.copyOf(numbers), read, left);
        if (shown != null) {
            return new Judgement.Stops(shown);
        }
        // Where the values ran out with the figure, more may be left untried, and that is said.
        return new Judgement.Unresolved(site, left[0] <= 0
                ? WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED
                : WhyAStopIsNotShown.NO_VALUE_FOUND);
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
     */
    private record Before(List<UndividedByARelation.IntOperation> operations,
                          List<UndividedByARelation.Division> divisions,
                          List<TakenConstraint.Affine> way) {}

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
            case Site.ByNought(var division) -> division.divisor();
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
        for (UndividedByARelation.Division other : before.divisions()) {
            ExactRatio divisor = WholeValuesMeeting.valueOf(other.divisor(), at);
            if (divisor == null || divisor.signum() == 0) {
                return false;
            }
        }
        return switch (site) {
            case Site.PastItsEnds(var operation) -> {
                ExactRatio comes = WholeValuesMeeting.valueOf(operation.overTheInput(), at);
                yield comes != null && !withinItsEnds(comes, operation);
            }
            case Site.ByNought(var division) -> {
                ExactRatio divisor = WholeValuesMeeting.valueOf(division.divisor(), at);
                yield divisor != null && divisor.signum() == 0;
            }
        };
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
