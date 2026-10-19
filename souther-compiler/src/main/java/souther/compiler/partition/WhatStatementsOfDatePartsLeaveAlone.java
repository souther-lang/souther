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
 * <p>The statements are of dates the caller has shown nothing restricts, and every term of them is
 * a month, a day or a year of one of those dates.
 */
final class WhatStatementsOfDatePartsLeaveAlone {

    /** The dates a way may state the parts of for them to be looked through together: the
     *  choices multiply, each date having a few hundred. */
    static final int MOST_DATES_A_WAY_IS_ASKED_OF = 2;

    /** The days in the longest month, which is as far as a part of a date runs. */
    private static final long GREATEST_PART = 31;

    private WhatStatementsOfDatePartsLeaveAlone() {
    }

    /**
     * Whether the years of the dates are left to the calendar by {@code statements} of their
     * months and days: some month and day of each date holds all of them at once, and is the same
     * in every year.
     *
     * @param yearShifts the moves of each date whose years are asked, which a month and day must
     *                   keep the date in the year of
     */
    static boolean leavesTheYears(List<TakenConstraint.Affine> statements,
                                  Map<TermPath, List<DateTranslation>> yearShifts) {
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
        List<List<NumericTerm.TakenOf>> terms = new ArrayList<>();
        List<List<DatesThatStandInEveryYear.Origin>> standing = new ArrayList<>();
        for (Map.Entry<TermPath, Set<NumericTerm.TakenOf>> date : partsOfEachDate.entrySet()) {
            List<NumericTerm.TakenOf> parts = List.copyOf(date.getValue());
            List<DatesThatStandInEveryYear.Part> asked = new ArrayList<>();
            for (NumericTerm.TakenOf part : parts) {
                asked.add(new DatesThatStandInEveryYear.Part(
                        ((TakenAs.PartOfDate) part.takenAs()).part(),
                        part.transformation().translation()));
            }
            List<DatesThatStandInEveryYear.Origin> alike = DatesThatStandInEveryYear.of(asked,
                    yearShifts.getOrDefault(date.getKey(), List.of()));
            if (alike.isEmpty()) {
                return false;
            }
            terms.add(parts);
            standing.add(alike);
        }
        return someChoiceHoldsAll(statements, terms, standing);
    }

    /**
     * The year each date is put in by {@code statements} of their years, at which the months and
     * days of the dates are left to the calendar: the years hold all the statements together,
     * and in each every month and day the sides take of the date still is one.
     *
     * @param partsAsked the months and days the sides take of each date
     * @return the years, with the moves the statements take the dates' years after, or null where
     *         there are none
     */
    static YearsChosen leavesTheMonthsAndDays(
            List<TakenConstraint.Affine> statements,
            Map<TermPath, List<DatesThatStandInEveryYear.Part>> partsAsked) {
        Map<TermPath, Integer> dates = new LinkedHashMap<>();
        Map<TermPath, List<DateTranslation>> shifts = new LinkedHashMap<>();
        List<YearsAWayAllows.Statement> asked = new ArrayList<>();
        for (TakenConstraint.Affine each : statements) {
            List<YearsAWayAllows.Year> years = new ArrayList<>();
            for (Map.Entry<NumericTerm, ExactRatio> term : each.form().coefs().entrySet()) {
                NumericTerm.TakenOf taken = (NumericTerm.TakenOf) term.getKey();
                int date = dates.computeIfAbsent(taken.position(), _ -> dates.size());
                DateTranslation moved = taken.transformation().translation();
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
            parts.add(partsAsked.getOrDefault(date, List.of()));
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
     * Whether every statement holds at some choice of a month and a day for each date.
     *
     * <p>A statement is a sum over the dates, so what a month and day of one date does to it is
     * the part of the sum its terms come to there, one number for each statement. Months and days
     * that come to the same numbers are one choice, and the choices of the dates are put
     * together on those numbers and not on the several hundred origins each date has.
     */
    private static boolean someChoiceHoldsAll(
            List<TakenConstraint.Affine> statements, List<List<NumericTerm.TakenOf>> terms,
            List<List<DatesThatStandInEveryYear.Origin>> standing) {
        long[] constants = new long[statements.size()];
        for (int i = 0; i < constants.length; i++) {
            Long constant = YearsAWayAllows.asLong(statements.get(i).form().constant());
            if (constant == null) {
                return false;
            }
            constants[i] = constant;
        }
        List<Set<List<Long>>> choices = new ArrayList<>();
        for (int date = 0; date < standing.size(); date++) {
            Set<List<Long>> here = new LinkedHashSet<>();
            for (DatesThatStandInEveryYear.Origin origin : standing.get(date)) {
                List<Long> part = partOfTheSums(statements, terms.get(date), origin);
                if (part == null) {
                    return false;
                }
                here.add(part);
            }
            choices.add(here);
        }
        return someChoiceHolds(statements, choices, 0, constants);
    }

    /** What the terms of one date come to in each statement at {@code origin}, or null where a
     *  weight or a part is not a whole number. */
    private static List<Long> partOfTheSums(List<TakenConstraint.Affine> statements,
                                            List<NumericTerm.TakenOf> terms,
                                            DatesThatStandInEveryYear.Origin origin) {
        List<Long> out = new ArrayList<>();
        for (TakenConstraint.Affine statement : statements) {
            long sum = 0;
            for (int j = 0; j < terms.size(); j++) {
                ExactRatio weight = statement.form().coefs().get(terms.get(j));
                if (weight == null) {
                    continue;
                }
                Long weighed = YearsAWayAllows.asLong(weight);
                Long part = YearsAWayAllows.asLong(origin.parts().get(j));
                if (weighed == null || part == null) {
                    return null;
                }
                sum += weighed * part;
            }
            out.add(sum);
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
