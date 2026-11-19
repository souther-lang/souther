package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.time.Month;
import java.time.YearMonth;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the calendar's cycle is read to give, a year of each kind at a time, is what walking every
 * day of the cycle gives; and each reader of it answers what it answered when it walked the
 * years itself. The walks are written here, one day and one year at a time.
 */
class WhatTheCycleGivesIsWhatEveryDayOfItGivesTest {

    private static final long FIRST_DAY = LocalDate.of(2000, 1, 1).toEpochDay();

    private static final long LAST_DAY = LocalDate.of(2399, 12, 31).toEpochDay();

    /** Moves at the edges of a month, a year, four years, a century and a cycle, and past. */
    private static final long[] MOVES = {0, 1, -1, 28, 59, -59, 306, -306, 365, -365, 366,
            1_461, -1_461, 36_524, 36_525, -36_524, 73_048, -73_049, 146_097, -146_097, 146_098,
            400_000, -400_000};

    private static final TakenAs.DatePart[] PARTS = TakenAs.DatePart.values();

    /** Moves of the table above, and some drawn at random, by a fixed draw. */
    private static long aMove(Random random) {
        return random.nextInt(3) == 0 ? random.nextInt(400_001) - 200_000
                : MOVES[random.nextInt(MOVES.length)];
    }

    /** What walking every day of a cycle gives, in the order a day first gives each list. */
    private static List<PartsOfADateOverACycle.Given> walked(
            List<PartsOfADateOverACycle.Moved> parts) {
        Map<List<Integer>, BitSet> out = new LinkedHashMap<>();
        for (long day = FIRST_DAY; day <= LAST_DAY; day++) {
            int year = LocalDate.ofEpochDay(day).getYear();
            List<Integer> values = new ArrayList<>();
            for (PartsOfADateOverACycle.Moved part : parts) {
                LocalDate moved = LocalDate.ofEpochDay(day + part.offsetDays());
                values.add(part.which() == TakenAs.DatePart.YEAR ? moved.getYear() - year
                        : part.which().of(moved));
            }
            out.computeIfAbsent(values, _ -> new BitSet()).set(Math.floorMod(year, 400));
        }
        List<PartsOfADateOverACycle.Given> given = new ArrayList<>();
        out.forEach((values, years) -> given.add(new PartsOfADateOverACycle.Given(values, years)));
        return given;
    }

    @Test
    void theCycleReadByKindsOfYearIsTheCycleWalkedDayByDay() {
        Random random = new Random(3298);
        for (int asked = 0; asked < 24; asked++) {
            List<PartsOfADateOverACycle.Moved> parts = new ArrayList<>();
            for (int each = random.nextInt(3); each >= 0; each--) {
                parts.add(new PartsOfADateOverACycle.Moved(PARTS[random.nextInt(PARTS.length)],
                        aMove(random)));
            }
            assertEquals(walked(parts), PartsOfADateOverACycle.of(parts), parts.toString());
        }
    }

    private static DatesThatStandInEveryYear.Part monthOrDay(Random random) {
        return new DatesThatStandInEveryYear.Part(random.nextBoolean() ? TakenAs.DatePart.MONTH
                : TakenAs.DatePart.DAY, DateTranslation.none().thenAddDays(aMove(random)));
    }

    /** The years of the cycle that give every number of each part, asked one year at a time. */
    @Test
    void theYearsGivingEveryNumberAreTheYearsThatDoOneAtATime() {
        Random random = new Random(3299);
        for (int asked = 0; asked < 24; asked++) {
            List<DatesThatStandInEveryYear.Part> parts = new ArrayList<>();
            for (int each = random.nextInt(2); each >= 0; each--) {
                parts.add(monthOrDay(random));
            }
            List<DateTranslation> shifts = new ArrayList<>();
            for (int each = random.nextInt(3); each > 0; each--) {
                shifts.add(DateTranslation.none().thenAddDays(aMove(random)));
            }
            BitSet oneAtATime = new BitSet();
            for (int year = 2000; year < 2400; year++) {
                if (MonthsAndDaysOfOneDate.coversEveryValueInYear(parts, year, shifts)) {
                    oneAtATime.set(year % 400);
                }
            }
            assertEquals(oneAtATime, YearsAWayAllows.classesGivingEveryValue(parts, shifts),
                    parts + " " + shifts);
        }
    }

    /**
     * The months and days at which the parts are the same in every year between two, and every
     * shift keeps the date in its year, asked of each month and day in each of those years: over
     * fewer years than a cycle, starting anywhere in it, and over more.
     */
    @Test
    void theMonthsAndDaysAlikeInTheYearsBetweenAreThoseAlikeInEachYear() {
        Random random = new Random(3300);
        for (int asked = 0; asked < 24; asked++) {
            List<DatesThatStandInEveryYear.Part> parts = new ArrayList<>();
            for (int each = random.nextInt(3); each > 0; each--) {
                parts.add(monthOrDay(random));
            }
            List<DateTranslation> shifts = new ArrayList<>();
            for (int each = random.nextInt(3); each > 0; each--) {
                shifts.add(DateTranslation.none().thenAddDays(
                        MOVES[random.nextInt(11)] * (random.nextBoolean() ? 1 : -1)));
            }
            int first = 1_000 + random.nextInt(2_000);
            int last = first + 2 + (random.nextBoolean() ? random.nextInt(20) : 380
                    + random.nextInt(60));
            assertEquals(alikeYearByYear(parts, shifts, first, last),
                    DatesThatStandInEveryYear.alikeInTheYearsBetween(parts, shifts, first, last),
                    parts + " " + shifts + " " + first + ".." + last);
        }
    }

    private static List<DatesThatStandInEveryYear.Origin> alikeYearByYear(
            List<DatesThatStandInEveryYear.Part> parts, List<DateTranslation> shifts,
            int first, int last) {
        int from = first + 1;
        int to = Math.min(last - 1, first + 400);
        List<DatesThatStandInEveryYear.Origin> out = new ArrayList<>();
        for (int month = 1; month <= 12; month++) {
            for (int day = 1; day <= Month.of(month).maxLength(); day++) {
                int[] alike = null;
                boolean every = true;
                for (int year = from; year <= to && every; year++) {
                    if (day > YearMonth.of(year, month).lengthOfMonth()) {
                        every = false;
                        break;
                    }
                    long origin = LocalDate.of(year, month, day).toEpochDay();
                    for (DateTranslation shift : shifts) {
                        every &= LocalDate.ofEpochDay(origin + shift.offsetDays()).getYear()
                                == year;
                    }
                    int[] here = new int[parts.size()];
                    for (int i = 0; i < here.length; i++) {
                        here[i] = parts.get(i).of(LocalDate.ofEpochDay(
                                origin + parts.get(i).moved().offsetDays()));
                    }
                    if (alike == null) {
                        alike = here;
                    } else {
                        every &= Arrays.equals(alike, here);
                    }
                }
                if (every) {
                    out.add(new DatesThatStandInEveryYear.Origin(month, day,
                            Arrays.stream(alike).mapToObj(ExactRatio::of).toList()));
                }
            }
        }
        return out;
    }

    /** The combinations a date anywhere gives, as a cycle of days walked one day at a time
     *  gives them. */
    @Test
    void theCombinationsOfAnyYearAreThoseOfEveryDayOfTheCycle() {
        Random random = new Random(3301);
        for (int asked = 0; asked < 24; asked++) {
            List<DatesThatStandInEveryYear.Part> parts = new ArrayList<>();
            for (int each = random.nextInt(3); each >= 0; each--) {
                parts.add(monthOrDay(random));
            }
            Set<List<ExactRatio>> walked = new LinkedHashSet<>();
            for (long day = FIRST_DAY; day <= LAST_DAY; day++) {
                List<ExactRatio> here = new ArrayList<>();
                for (DatesThatStandInEveryYear.Part part : parts) {
                    here.add(ExactRatio.of(part.of(LocalDate.ofEpochDay(
                            day + part.moved().offsetDays()))));
                }
                walked.add(here);
            }
            assertEquals(List.copyOf(walked), MonthsAndDaysOfOneDate.ofAnyYear(parts),
                    parts.toString());
        }
    }
}
