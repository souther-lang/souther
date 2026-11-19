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
import java.util.stream.LongStream;

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
 * <p>Only for a date no rule restricts but ends on the days it may be. A rule on a part of it
 * leaves the combinations that rule lets through, which this does not read; the caller does not
 * ask.
 */
final class MonthsAndDaysOfOneDate {

    private MonthsAndDaysOfOneDate() {
    }

    /**
     * Every combination of {@code parts} of one date at some day every move of them is defined
     * at, in the order of {@code parts}, or null where there is no such day.
     *
     * <p>A cycle of days holds every combination there is, so where the days are a cycle or more
     * what one cycle gives is read, each part over it
     * ({@link DatesThatStandInEveryYear.Part#overACycle}): a fact of the calendar and of what the
     * moves move by, kept for every compilation. A date
     * held to fewer days gives what those give, and may miss the twenty-ninth of February or what
     * a move makes of the last days of a year: that turns on the dates a model holds the date to,
     * and is worked out where it is asked.
     */
    static List<List<ExactRatio>> ofAnyYear(List<DatesThatStandInEveryYear.Part> parts) {
        DateTranslation every = DateTranslation.none();
        for (DatesThatStandInEveryYear.Part part : parts) {
            every = every == null ? null : every.definedOnlyWhere(part.moved());
        }
        if (every == null) {
            return null;
        }
        if (every.last() - every.first() + 1 < DatePartsLeft.DAYS_OF_A_CYCLE) {
            return workedOverTheDays(parts, every.first(), every.last());
        }
        List<DatesThatStandInEveryYear.Part> overACycle = parts.stream()
                .map(DatesThatStandInEveryYear.Part::overACycle).toList();
        return EVERY_YEAR.computeIfAbsent(overACycle, asked -> workedOverTheDays(asked,
                HeldClass.A_CYCLE_STARTS,
                HeldClass.A_CYCLE_STARTS + DatePartsLeft.DAYS_OF_A_CYCLE - 1));
    }

    /** Answers by what was asked, which is all there is to them: the calendar and what the moves
     *  move by over a cycle. A program asks the same few moves again and again, and each answer
     *  walks a cycle of the calendar. */
    private static final Map<List<DatesThatStandInEveryYear.Part>, List<List<ExactRatio>>>
            EVERY_YEAR = new ConcurrentHashMap<>();

    /** Every combination of {@code parts} at the days from {@code from} to {@code to}, at every
     *  one of which every move of them is defined. */
    private static List<List<ExactRatio>> workedOverTheDays(
            List<DatesThatStandInEveryYear.Part> parts, long from, long to) {
        // The numbers are compared as numbers, and only the combinations that differ are made into
        // ratios: a cycle has far more days than it has distinct combinations.
        Set<Combination> seen = new LinkedHashSet<>();
        LongStream.rangeClosed(from, to)
                .forEach(day -> seen.add(new Combination(numbersAt(parts, day))));
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
        DatesThatStandInEveryYear.DaysOfAYear days = DatesThatStandInEveryYear.DaysOfAYear.of(year);
        long first = days.first();
        long last = days.last();
        for (long day = first; day <= last; day++) {
            if (staysInTheYear(yearShifts, day, days)) {
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
        DatesThatStandInEveryYear.DaysOfAYear days = DatesThatStandInEveryYear.DaysOfAYear.of(year);
        long first = days.first();
        long last = days.last();
        for (long day = first; day <= last; day++) {
            if (!staysInTheYear(yearShifts, day, days)) {
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

    private static boolean staysInTheYear(List<DateTranslation> yearShifts, long day,
                                          DatesThatStandInEveryYear.DaysOfAYear year) {
        for (DateTranslation each : yearShifts) {
            if (!each.definedAt(day) || !year.holds(day + each.offsetDays())) {
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
