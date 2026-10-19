package souther.compiler.partition;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The years a way that states the years of dates puts them in, one year for each date, so that
 * what the months and days of those dates come to can be read in those years.
 *
 * <p>A way that states years ties the months and days of the dates only through the years: a
 * year with no twenty-ninth of February has no date with one. So the months and days are left to
 * the calendar not when the statements leave every year, but when there are years for the dates
 * that hold them all together and in which every month and every day still is one. Two statements
 * that each hold at many years may hold at one only together — {@code year >= 2025} with
 * {@code year <= 2025}, or a difference of two years held to sixty by a statement from above and
 * one from below — and the years chosen are years of that one.
 *
 * <p>The years are looked for among the eight hundred years from a fixed start, two cycles of the
 * calendar, which are far from its ends: every move is defined there, and the pattern of leap
 * years that a date can be in appears twice. A way no years there hold is not shown to leave the
 * months and days anything.
 */
final class YearsAWayAllows {

    /** A year of a date, as the weight the statement gives it and the move of the date before
     *  its year is taken. */
    record Year(int date, ExactRatio weight, DateTranslation moved) {}

    /** {@code constant} and the weighed {@code years} held against nought as {@code relation}. */
    record Statement(List<Year> years, ExactRatio constant, Rel relation) {}

    private static final int FIRST_YEAR = 2000;
    private static final int YEARS_ASKED = 800;

    private YearsAWayAllows() {
    }

    /**
     * A year for each date, in the order of {@code partsOfEachDate}, at which every statement holds
     * and in which each date gives every number each of its parts can be — or null where there
     * are none.
     *
     * <p>A date's days in a year are those {@code statements} leave it in: the days at which a
     * move of the date does not take it to another year. The statements are then about that year,
     * whatever the day.
     *
     * @param partsOfEachDate the months and days taken of each date, which must each appear in the
     *                        year chosen for it
     */
    static int[] choose(List<Statement> statements,
                        List<List<DatesThatStandInEveryYear.Part>> partsOfEachDate) {
        List<long[]> weights = new ArrayList<>();
        List<Long> constants = new ArrayList<>();
        for (Statement each : statements) {
            long[] ofEachDate = new long[partsOfEachDate.size()];
            for (Year year : each.years()) {
                Long weight = asLong(year.weight());
                if (weight == null) {
                    return null;
                }
                ofEachDate[year.date()] += weight;
            }
            Long constant = asLong(each.constant());
            if (constant == null || !staysInsideTheType(ofEachDate, constant)) {
                return null;
            }
            weights.add(ofEachDate);
            constants.add(constant);
        }
        List<List<Integer>> candidates = new ArrayList<>();
        for (int date = 0; date < partsOfEachDate.size(); date++) {
            candidates.add(yearsGivingEveryValue(date, statements, partsOfEachDate.get(date)));
            if (candidates.get(date).isEmpty()) {
                return null;
            }
        }
        return search(statements, weights, constants, candidates, new int[candidates.size()], 0);
    }

    private static int[] search(List<Statement> statements, List<long[]> weights,
                                List<Long> constants, List<List<Integer>> candidates,
                                int[] chosen, int date) {
        if (date == candidates.size()) {
            for (int i = 0; i < statements.size(); i++) {
                long sum = constants.get(i);
                for (int each = 0; each < chosen.length; each++) {
                    sum += weights.get(i)[each] * chosen[each];
                }
                if (!statements.get(i).relation().holds(Long.signum(sum))) {
                    return null;
                }
            }
            return chosen.clone();
        }
        for (int year : candidates.get(date)) {
            chosen[date] = year;
            int[] found = search(statements, weights, constants, candidates, chosen, date + 1);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    /** The years among those asked in which the date gives every number each part can be. */
    private static List<Integer> yearsGivingEveryValue(int date, List<Statement> statements,
                                                       List<DatesThatStandInEveryYear.Part> parts) {
        List<DateTranslation> yearShifts = new ArrayList<>();
        for (Statement statement : statements) {
            for (Year year : statement.years()) {
                if (year.date() == date) {
                    yearShifts.add(year.moved());
                }
            }
        }
        return GIVING_EVERY_VALUE.computeIfAbsent(new Asked(List.copyOf(parts), yearShifts),
                asked -> worked(asked.parts(), asked.yearShifts()));
    }

    /** What was asked of the calendar, which is all there is to the answer. */
    private record Asked(List<DatesThatStandInEveryYear.Part> parts,
                         List<DateTranslation> yearShifts) {}

    /** Answers by what was asked. The same few moves come back across the relations of a program,
     *  and each answer looks through two cycles of the calendar. */
    private static final Map<Asked, List<Integer>> GIVING_EVERY_VALUE = new ConcurrentHashMap<>();

    private static List<Integer> worked(List<DatesThatStandInEveryYear.Part> parts,
                                        List<DateTranslation> yearShifts) {
        List<Integer> out = new ArrayList<>();
        for (int year = FIRST_YEAR; year < FIRST_YEAR + YEARS_ASKED; year++) {
            List<List<ExactRatio>> given = MonthsAndDaysOfOneDate.inYear(parts, year, yearShifts);
            if (!given.isEmpty() && MonthsAndDaysOfOneDate.coversEveryValue(given, parts)) {
                out.add(year);
            }
        }
        return out;
    }

    /** The whole number {@code value} is, or null where it is not one or the type does not hold
     *  it. */
    static Long asLong(ExactRatio value) {
        if (!value.isWhole()) {
            return null;
        }
        BigInteger whole = value.floor().orNull();
        return whole == null || whole.bitLength() > Long.SIZE - 2 ? null : whole.longValue();
    }

    /**
     * Whether the weighed years of a statement come to a number the type holds at any year asked:
     * a row is one the program runs, and a sum past the type's greatest is where it stops.
     */
    private static boolean staysInsideTheType(long[] weights, long constant) {
        BigInteger size = BigInteger.valueOf(constant).abs();
        BigInteger farthest = BigInteger.valueOf(FIRST_YEAR + YEARS_ASKED);
        for (long weight : weights) {
            size = size.add(BigInteger.valueOf(weight).abs().multiply(farthest));
        }
        return size.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) <= 0;
    }
}
