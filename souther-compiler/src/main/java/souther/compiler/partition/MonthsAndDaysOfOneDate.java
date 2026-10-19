package souther.compiler.partition;

import souther.compiler.check.DatePartsLeft;
import souther.compiler.check.HeldClass;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The months and days that go together, for numbers taken of one date that nothing restricts.
 *
 * <p>A month and a day of one date are two numbers, and not every month goes with every day. The
 * combinations are the calendar's, and the calendar repeats every four hundred years, so one cycle
 * of days has them all. A part taken after the date was moved by a number of days is the part of
 * the date that many days on, so it is read at the same day of the cycle.
 *
 * <p>Where a way fixes the year of the date, the combinations are those of that year: a year with
 * no twenty-ninth of February gives none that has one. Only the combinations the year gives are
 * reachable, and a combination is a witness only for what it is reachable for; what the caller
 * must still know is that every number the parts can be appears in them
 * ({@link #coversEveryValue}).
 *
 * <p>Only for a date no rule restricts. A rule on a part of it, or on the days it may be, leaves
 * the combinations that rule lets through, which this does not read; the caller does not ask.
 */
final class MonthsAndDaysOfOneDate {

    private MonthsAndDaysOfOneDate() {
    }

    /**
     * Every combination of {@code parts} of one date in any year, in the order of {@code parts},
     * or null where a move is not defined at every day of the cycle.
     */
    static List<List<ExactRatio>> ofAnyYear(List<DatesThatStandInEveryYear.Part> parts) {
        return EVERY_YEAR.computeIfAbsent(List.copyOf(parts),
                asked -> new Combinations(workedOverTheCycle(asked))).combinations();
    }

    /** The combinations, which are none where a move is not defined. */
    private record Combinations(List<List<ExactRatio>> combinations) {}

    /** Answers by what was asked, which is all there is to them: the calendar and the moves. A
     *  program asks the same few moves again and again, and each answer walks a cycle of the
     *  calendar. */
    private static final Map<List<DatesThatStandInEveryYear.Part>, Combinations> EVERY_YEAR =
            new ConcurrentHashMap<>();

    private record AskedOfAYear(List<DatesThatStandInEveryYear.Part> parts, int year,
                                List<DateTranslation> yearShifts) {}

    private static final Map<AskedOfAYear, List<List<ExactRatio>>> OF_A_YEAR =
            new ConcurrentHashMap<>();

    private static List<List<ExactRatio>> workedOverTheCycle(
            List<DatesThatStandInEveryYear.Part> parts) {
        Set<List<ExactRatio>> out = new LinkedHashSet<>();
        for (long day = HeldClass.A_CYCLE_STARTS;
                day < HeldClass.A_CYCLE_STARTS + DatePartsLeft.DAYS_OF_A_CYCLE; day++) {
            List<ExactRatio> combination = combinationAt(parts, day);
            if (combination == null) {
                return null;
            }
            out.add(combination);
        }
        return List.copyOf(out);
    }

    /**
     * Every combination of {@code parts} of one date in {@code year}, at the days of it that
     * {@code yearShifts} leave in the year and are defined at, or none where there is no such day.
     *
     * <p>The combinations at a day that a move leaves undefined are not reachable and are left
     * out. A day a move of {@code yearShifts} takes to another year is left out too, because the
     * year the caller asked about is then not the year of that date.
     */
    static List<List<ExactRatio>> inYear(List<DatesThatStandInEveryYear.Part> parts, int year,
                                         List<DateTranslation> yearShifts) {
        return OF_A_YEAR.computeIfAbsent(
                new AskedOfAYear(List.copyOf(parts), year, List.copyOf(yearShifts)),
                asked -> workedInYear(asked.parts(), asked.year(), asked.yearShifts()));
    }

    private static List<List<ExactRatio>> workedInYear(
            List<DatesThatStandInEveryYear.Part> parts, int year,
            List<DateTranslation> yearShifts) {
        Set<List<ExactRatio>> out = new LinkedHashSet<>();
        long first = LocalDate.of(year, 1, 1).toEpochDay();
        long last = LocalDate.of(year, 12, 31).toEpochDay();
        for (long day = first; day <= last; day++) {
            if (staysInTheYear(yearShifts, day, year)) {
                List<ExactRatio> combination = combinationAt(parts, day);
                if (combination != null) {
                    out.add(combination);
                }
            }
        }
        return List.copyOf(out);
    }

    /** Whether every one of {@code combinations} is the number each of {@code parts} can be: a
     *  month from one to twelve and a day from one to thirty-one all appear. */
    static boolean coversEveryValue(List<List<ExactRatio>> combinations,
                                    List<DatesThatStandInEveryYear.Part> parts) {
        for (int i = 0; i < parts.size(); i++) {
            int at = i;
            long values = combinations.stream().map(each -> each.get(at)).distinct().count();
            long every = parts.get(i).which() == TakenAs.DatePart.MONTH ? 12 : 31;
            if (values != every) {
                return false;
            }
        }
        return true;
    }

    private static boolean staysInTheYear(List<DateTranslation> yearShifts, long day, int year) {
        for (DateTranslation each : yearShifts) {
            if (!each.definedAt(day)
                    || LocalDate.ofEpochDay(day + each.offsetDays()).getYear() != year) {
                return false;
            }
        }
        return true;
    }

    private static List<ExactRatio> combinationAt(List<DatesThatStandInEveryYear.Part> parts,
                                                  long day) {
        List<ExactRatio> combination = new ArrayList<>();
        for (DatesThatStandInEveryYear.Part part : parts) {
            if (!part.moved().definedAt(day)) {
                return null;
            }
            LocalDate date = LocalDate.ofEpochDay(day + part.moved().offsetDays());
            combination.add(ExactRatio.of(part.which() == TakenAs.DatePart.MONTH
                    ? date.getMonthValue() : date.getDayOfMonth()));
        }
        return combination;
    }
}
