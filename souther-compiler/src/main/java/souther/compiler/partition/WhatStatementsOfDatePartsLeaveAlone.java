package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Whether what a way states of one kind of part of dates leaves the other kind to the calendar.
 *
 * <p>The way is asked whole, and not a statement at a time. Two statements that each hold at a
 * stretch of years may hold at no year together — {@code year >= 2025} and {@code year <= 2025}
 * — and then a month and a day the first lets through are not in the year the second allows. So
 * what is shown is that all the statements of one kind hold at once: at one month and day of each
 * date that is the same in every year, or at one year of each date in which every month and day
 * is still one.
 *
 * <p>The statements are of dates the caller has shown nothing restricts but ends on the date,
 * which are told as the days each may be, and every term of them is a month, a day or a year of
 * one of those dates.
 */
final class WhatStatementsOfDatePartsLeaveAlone {

    /** The dates a way may state the parts of for them to be looked through together: the
     *  choices multiply, each date having a few hundred. */
    static final int MOST_DATES_A_WAY_IS_ASKED_OF = 2;

    /** The days in the longest month, which is as far as a part of a date runs. */
    private static final long GREATEST_PART = TakenAs.DatePart.DAY.greatest();

    private WhatStatementsOfDatePartsLeaveAlone() {
    }

    /**
     * Whether the years of the dates are left to the calendar by {@code statements} of their
     * months and days: in each kind of year each date has, some month and day of it holds all of
     * them at once together with one of each kind of year the other has, so that every year of
     * the one goes with every year of the other ({@link DatesThatStandInEveryYear#byTheYearsOf}).
     *
     * @param yearShifts the moves of each date whose years are asked, which a month and day must
     *                   keep the date in the year of
     * @param days       the dates each date may be, as the days a move by nothing is defined at
     */
    static boolean leavesTheYears(List<TakenConstraint.Affine> statements,
                                  Map<TermPath, List<DateTranslation>> yearShifts,
                                  Map<TermPath, DateTranslation> days) {
        Map<TermPath, Set<NumericTerm.TakenOf>> partsOfEachDate = new LinkedHashMap<>();
        for (TakenConstraint.Affine each : statements) {
            for (NumericTerm term : each.form().coefs().keySet()) {
                NumericTerm.TakenOf taken = (NumericTerm.TakenOf) term;
                partsOfEachDate.computeIfAbsent(taken.position(), _ -> new LinkedHashSet<>())
                        .add(taken);
            }
        }
        if (partsOfEachDate.isEmpty() || partsOfEachDate.size() > MOST_DATES_A_WAY_IS_ASKED_OF
                || !stayInsideTheType(statements)) {
            return false;
        }
        long[] constants = new long[statements.size()];
        for (int i = 0; i < constants.length; i++) {
            Long constant = YearsAWayAllows.asLongOrNull(statements.get(i).form().constant());
            if (constant == null) {
                return false;
            }
            constants[i] = constant;
        }
        List<List<Set<List<Long>>>> kinds = new ArrayList<>();
        for (Map.Entry<TermPath, Set<NumericTerm.TakenOf>> date : partsOfEachDate.entrySet()) {
            List<NumericTerm.TakenOf> parts = List.copyOf(date.getValue());
            DateTranslation held = days.get(date.getKey());
            List<DatesThatStandInEveryYear.Part> asked = new ArrayList<>();
            for (NumericTerm.TakenOf part : parts) {
                DateTranslation moved = within(part.transformation().translation(), held);
                if (moved == null) {
                    return false;
                }
                asked.add(new DatesThatStandInEveryYear.Part(
                        ((TakenAs.PartOfDate) part.takenAs()).part(), moved));
            }
            List<DateTranslation> shifts = new ArrayList<>();
            for (DateTranslation each : yearShifts.getOrDefault(date.getKey(), List.of())) {
                DateTranslation moved = within(each, held);
                if (moved == null) {
                    return false;
                }
                shifts.add(moved);
            }
            List<List<DatesThatStandInEveryYear.Origin>> ofTheYears =
                    DatesThatStandInEveryYear.byTheYearsOf(asked, shifts);
            List<Set<List<Long>>> sums = ofTheYears == null ? null
                    : partsOfTheSums(statements, parts, ofTheYears);
            if (sums == null) {
                return false;
            }
            kinds.add(sums);
        }
        return everyKindHoldsAll(statements, constants, kinds, new ArrayList<>());
    }

    /** {@code move}, defined only at the dates {@code days} says the date may be, or null where
     *  nothing says or that leaves none. */
    private static DateTranslation within(DateTranslation move, DateTranslation days) {
        return days == null ? null : move.definedOnlyWhere(days);
    }

    /** Whether some choice holds every statement at each kind of year of each date, taken with
     *  each kind of the dates after it: {@code chosen} holds the kinds taken of those before, as
     *  the parts of the sums their months and days come to ({@link #partsOfTheSums}). */
    private static boolean everyKindHoldsAll(List<TakenConstraint.Affine> statements,
                                             long[] constants,
                                             List<List<Set<List<Long>>>> kinds,
                                             List<Set<List<Long>>> chosen) {
        if (chosen.size() == kinds.size()) {
            return someChoiceHolds(statements, chosen, 0, constants);
        }
        for (Set<List<Long>> kind : kinds.get(chosen.size())) {
            chosen.add(kind);
            boolean holds = everyKindHoldsAll(statements, constants, kinds, chosen);
            chosen.removeLast();
            if (!holds) {
                return false;
            }
        }
        return true;
    }

    /**
     * The year each date is put in by {@code statements} of their years, at which the months and
     * days of the dates are left to the calendar: the years hold all the statements together,
     * and in each every month and day the sides take of the date still is one.
     *
     * <p>Each move is told the dates its date may be first, so a year is chosen only where every
     * month and day asked is one of them ({@link YearsAWayAllows#choose}).
     *
     * @param partsAsked the months and days the sides take of each date
     * @param days       the dates each date may be, as the days a move by nothing is defined at
     * @return the years, with the moves the statements take the dates' years after, or null where
     *         there are none
     */
    static YearsChosen leavesTheMonthsAndDays(
            List<TakenConstraint.Affine> statements,
            Map<TermPath, List<DatesThatStandInEveryYear.Part>> partsAsked,
            Map<TermPath, DateTranslation> days) {
        Map<TermPath, Integer> dates = new LinkedHashMap<>();
        Map<TermPath, List<DateTranslation>> shifts = new LinkedHashMap<>();
        List<YearsAWayAllows.Statement> asked = new ArrayList<>();
        for (TakenConstraint.Affine each : statements) {
            List<YearsAWayAllows.Year> years = new ArrayList<>();
            for (Map.Entry<NumericTerm, ExactRatio> term : each.form().coefs().entrySet()) {
                NumericTerm.TakenOf taken = (NumericTerm.TakenOf) term.getKey();
                int date = dates.computeIfAbsent(taken.position(), _ -> dates.size());
                DateTranslation moved = within(taken.transformation().translation(),
                        days.get(taken.position()));
                if (moved == null) {
                    return null;
                }
                years.add(new YearsAWayAllows.Year(date, term.getValue(), moved));
                shifts.computeIfAbsent(taken.position(), _ -> new ArrayList<>()).add(moved);
            }
            asked.add(new YearsAWayAllows.Statement(years, each.form().constant(), each.rel()));
        }
        if (asked.isEmpty() || dates.size() > MOST_DATES_A_WAY_IS_ASKED_OF) {
            return null;
        }
        List<List<DatesThatStandInEveryYear.Part>> parts = new ArrayList<>();
        for (TermPath date : dates.keySet()) {
            List<DatesThatStandInEveryYear.Part> ofIt = new ArrayList<>();
            for (DatesThatStandInEveryYear.Part part : partsAsked.getOrDefault(date, List.of())) {
                DateTranslation moved = within(part.moved(), days.get(date));
                if (moved == null) {
                    return null;
                }
                ofIt.add(new DatesThatStandInEveryYear.Part(part.which(), moved));
            }
            parts.add(ofIt);
        }
        int[] chosen = YearsAWayAllows.choose(asked, parts);
        if (chosen == null) {
            return null;
        }
        Map<TermPath, Integer> yearOf = new LinkedHashMap<>();
        dates.forEach((date, at) -> yearOf.put(date, chosen[at]));
        return new YearsChosen(yearOf, shifts);
    }

    /**
     * The year each date is in, and the moves the statements that chose it take the date's year
     * after, which the days it can be at are those that stay in the year.
     */
    record YearsChosen(Map<TermPath, Integer> yearOf,
                       Map<TermPath, List<DateTranslation>> shiftsOf) {}

    /**
     * For each kind of year of one date, the choices of a month and a day it gives, as what
     * {@code terms} come to in each statement there; null where a weight or a part is not a whole
     * number.
     *
     * <p>A statement is a sum over the dates, so what a month and day of one date does to it is
     * the part of the sum its terms come to there, one number for each statement. Months and days
     * that come to the same numbers are one choice, and the choices of the dates are put
     * together on those numbers and not on the several hundred origins each date has. Worked out
     * once per date, and not again for every kind of the other dates it is taken with.
     */
    private static List<Set<List<Long>>> partsOfTheSums(
            List<TakenConstraint.Affine> statements, List<NumericTerm.TakenOf> terms,
            List<List<DatesThatStandInEveryYear.Origin>> kinds) {
        // Each weight once, nought where a statement does not weigh the term.
        long[][] weights = new long[statements.size()][terms.size()];
        for (int i = 0; i < weights.length; i++) {
            for (int j = 0; j < terms.size(); j++) {
                ExactRatio weight = statements.get(i).form().coefs().get(terms.get(j));
                Long weighed = weight == null ? Long.valueOf(0)
                        : YearsAWayAllows.asLongOrNull(weight);
                if (weighed == null) {
                    return null;
                }
                weights[i][j] = weighed;
            }
        }
        List<Set<List<Long>>> out = new ArrayList<>();
        for (List<DatesThatStandInEveryYear.Origin> kind : kinds) {
            Set<List<Long>> here = new LinkedHashSet<>();
            for (DatesThatStandInEveryYear.Origin origin : kind) {
                long[] parts = new long[terms.size()];
                for (int j = 0; j < parts.length; j++) {
                    Long part = YearsAWayAllows.asLongOrNull(origin.parts().get(j));
                    if (part == null) {
                        return null;
                    }
                    parts[j] = part;
                }
                List<Long> sums = new ArrayList<>(weights.length);
                for (long[] weighs : weights) {
                    long sum = 0;
                    for (int j = 0; j < parts.length; j++) {
                        sum += weighs[j] * parts[j];
                    }
                    sums.add(sum);
                }
                here.add(sums);
            }
            out.add(here);
        }
        return out;
    }

    /** Whether the dates from {@code date} on can be chosen so that every statement, which the
     *  dates before it brought to {@code sofar}, holds. */
    private static boolean someChoiceHolds(List<TakenConstraint.Affine> statements,
                                           List<Set<List<Long>>> choices, int date,
                                           long[] sofar) {
        if (date == choices.size()) {
            for (int i = 0; i < sofar.length; i++) {
                if (!statements.get(i).rel().holds(Long.signum(sofar[i]))) {
                    return false;
                }
            }
            return true;
        }
        for (List<Long> part : choices.get(date)) {
            long[] next = sofar.clone();
            for (int i = 0; i < next.length; i++) {
                next[i] += part.get(i);
            }
            if (someChoiceHolds(statements, choices, date + 1, next)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether the weighed parts of each statement come to a number the type holds at any month
     * and day: a row is one the program runs, and a sum past the type's greatest is where it stops.
     */
    private static boolean stayInsideTheType(List<TakenConstraint.Affine> statements) {
        ExactRatio greatest = ExactRatio.of(Long.MAX_VALUE);
        for (TakenConstraint.Affine each : statements) {
            ExactRatio size = each.form().constant().abs();
            for (ExactRatio weight : each.form().coefs().values()) {
                size = weight.abs().times(ExactRatio.of(GREATEST_PART)).flatMap(size::plus)
                        .orNull();
                if (size == null) {
                    return false;
                }
            }
            if (size.compareTo(greatest) > 0) {
                return false;
            }
        }
        return true;
    }
}
