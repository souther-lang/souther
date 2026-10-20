package souther.compiler.partition;

import souther.compiler.check.DatePartsLeft;
import souther.compiler.check.HeldClass;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.Arrays;
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

    private static List<List<ExactRatio>> workedOverTheCycle(
            List<DatesThatStandInEveryYear.Part> parts) {
        // The numbers are compared as numbers, and only the combinations that differ are made into
        // ratios: a cycle is a hundred thousand days and a few hundred combinations.
        Set<Combination> seen = new LinkedHashSet<>();
        for (long day = HeldClass.A_CYCLE_STARTS;
                day < HeldClass.A_CYCLE_STARTS + DatePartsLeft.DAYS_OF_A_CYCLE; day++) {
            int[] numbers = numbersAt(parts, day);
            if (numbers == null) {
                return null;
            }
            seen.add(new Combination(numbers));
        }
        List<List<ExactRatio>> out = new ArrayList<>(seen.size());
        for (Combination each : seen) {
            out.add(ratiosOf(each.numbers()));
        }
        return List.copyOf(out);
    }

    /** The numbers the parts come to at one day, compared by what they are. */
    private static final class Combination {

        private final int[] numbers;

        Combination(int[] numbers) {
            this.numbers = numbers;
        }

        int[] numbers() {
            return numbers;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Combination that && Arrays.equals(numbers, that.numbers);
        }

        @Override
        public int hashCode() {
            return Arrays.hashCode(numbers);
        }
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

    /**
     * Whether the date in {@code year} gives every number each of {@code parts} can be, at the
     * days {@link #inYear} would keep: a month from one to twelve and a day from one to
     * thirty-one all appear, and some day is kept.
     *
     * <p>The same question as {@link #coversEveryValue} asked of {@link #inYear}, and answered
     * without building the combinations: a year is looked at to see which numbers appear, not what
     * goes with what.
     */
    static boolean coversEveryValueInYear(List<DatesThatStandInEveryYear.Part> parts, int year,
                                          List<DateTranslation> yearShifts) {
        long[] seen = new long[parts.size()];
        boolean kept = false;
        long first = LocalDate.of(year, 1, 1).toEpochDay();
        long last = LocalDate.of(year, 12, 31).toEpochDay();
        for (long day = first; day <= last; day++) {
            if (!staysInTheYear(yearShifts, day, year)) {
                continue;
            }
            boolean defined = true;
            for (DatesThatStandInEveryYear.Part part : parts) {
                defined &= part.moved().definedAt(day);
            }
            if (!defined) {
                continue;
            }
            kept = true;
            for (int i = 0; i < seen.length; i++) {
                DatesThatStandInEveryYear.Part part = parts.get(i);
                LocalDate date = LocalDate.ofEpochDay(day + part.moved().offsetDays());
                seen[i] |= 1L << part.of(date);
            }
        }
        for (int i = 0; i < seen.length; i++) {
            long every = (1L << (parts.get(i).howManyThereAre() + 1)) - 2;
            if (seen[i] != every) {
                return false;
            }
        }
        return kept;
    }

    /** Whether every one of {@code combinations} is the number each of {@code parts} can be: a
     *  month from one to twelve and a day from one to thirty-one all appear. */
    static boolean coversEveryValue(List<List<ExactRatio>> combinations,
                                    List<DatesThatStandInEveryYear.Part> parts) {
        for (int i = 0; i < parts.size(); i++) {
            int at = i;
            long values = combinations.stream().map(each -> each.get(at)).distinct().count();
            if (values != parts.get(i).howManyThereAre()) {
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
        int[] numbers = numbersAt(parts, day);
        return numbers == null ? null : ratiosOf(numbers);
    }

    /** What each of {@code parts} comes to at {@code day}, or null where a move is not defined
     *  there. */
    private static int[] numbersAt(List<DatesThatStandInEveryYear.Part> parts, long day) {
        int[] numbers = new int[parts.size()];
        for (int i = 0; i < numbers.length; i++) {
            DatesThatStandInEveryYear.Part part = parts.get(i);
            if (!part.moved().definedAt(day)) {
                return null;
            }
            numbers[i] = part.of(LocalDate.ofEpochDay(day + part.moved().offsetDays()));
        }
        return numbers;
    }

    private static List<ExactRatio> ratiosOf(int[] numbers) {
        List<ExactRatio> ratios = new ArrayList<>(numbers.length);
        for (int number : numbers) {
            ratios.add(ExactRatio.of(number));
        }
        return ratios;
    }
}
