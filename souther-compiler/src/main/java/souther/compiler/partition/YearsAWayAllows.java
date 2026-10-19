package souther.compiler.partition;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.BitSet;
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
 * <p>The years are found from the statements. Together they say between which years a date lies
 * for some year of the other to go with it, and the dates are chosen in turn: a few years in the
 * middle of the interval that is left and at each end of it. The calendar comes in only to say which of those years give
 * every month and day, and it repeats every four hundred years, so that is worked out once for the
 * four hundred and a year is turned away without being looked at. A year taken is then looked at
 * itself, so that nothing rests on the repetition holding at the calendar's ends, where a move is
 * defined at fewer dates.
 *
 * <p>Whole numbers are what a statement is held to, and they are added as exact numbers: the
 * weights come to a number the type holds at the farthest year there is, every weight counted
 * alone, so that no way of adding them stops the program where the sum would not.
 */
final class YearsAWayAllows {

    /** A year of a date, as the weight the statement gives it and the move of the date before
     *  its year is taken. */
    record Year(int date, ExactRatio weight, DateTranslation moved) {}

    /** {@code constant} and the weighed {@code years} held against nought as {@code relation}. */
    record Statement(List<Year> years, ExactRatio constant, Rel relation) {}

    private static final int YEARS_OF_A_CYCLE = 400;

    /** The first and the last year the calendar has. A move defined at fewer dates is asked of a
     *  year when it is chosen, not by leaving the ends out here. */
    private static final long LEAST_YEAR = LocalDate.MIN.getYear();
    private static final long GREATEST_YEAR = LocalDate.MAX.getYear();

    /** The year the middle of the calendar's use is taken to be, which is where a year is looked
     *  for first. */
    private static final long USUAL_YEAR = 2_000;

    /** The dates a way may state the years of for them to be chosen together: the years of one
     *  are looked for among those of the other, so the choices multiply. */
    private static final int MOST_DATES = 2;

    private YearsAWayAllows() {
    }

    /**
     * A year for each date, in the order of {@code partsOfEachDate}, at which every statement holds
     * and in which each date gives every number each of its parts can be — or null where none is
     * found.
     *
     * <p>A date's days in a year are those at which no move a statement takes its year after
     * puts the date in another year. The statements are then about that year, whatever the day.
     *
     * @param partsOfEachDate the months and days taken of each date, which must each appear in the
     *                        year chosen for it
     */
    static int[] choose(List<Statement> statements,
                        List<List<DatesThatStandInEveryYear.Part>> partsOfEachDate) {
        int dates = partsOfEachDate.size();
        if (dates == 0 || dates > MOST_DATES || !staysInsideTheType(statements)) {
            return null;
        }
        long[][] weights = new long[statements.size()][dates];
        long[] constants = new long[statements.size()];
        for (int i = 0; i < constants.length; i++) {
            constants[i] = asLong(statements.get(i).constant());
            for (Year year : statements.get(i).years()) {
                // Cannot pass the type: every weight was counted alone against the farthest year.
                weights[i][year.date()] += asLong(year.weight());
            }
        }
        List<List<DateTranslation>> shifts = new ArrayList<>();
        for (int date = 0; date < dates; date++) {
            shifts.add(shiftsOf(statements, date));
        }
        BitSet[] giving = new BitSet[dates];
        for (int date = 0; date < dates; date++) {
            giving[date] = classesGivingEveryValue(partsOfEachDate.get(date), shifts.get(date));
        }
        long[] chosen = new long[dates];
        return search(statements, weights, constants, partsOfEachDate, shifts, giving, chosen, 0)
                ? toInts(chosen) : null;
    }

    private static int[] toInts(long[] years) {
        int[] out = new int[years.length];
        for (int i = 0; i < out.length; i++) {
            out[i] = (int) years[i];
        }
        return out;
    }

    /**
     * Whether the dates from {@code date} on can be put in years that, with those already chosen,
     * hold every statement.
     */
    private static boolean search(List<Statement> statements, long[][] weights, long[] constants,
                                  List<List<DatesThatStandInEveryYear.Part>> parts,
                                  List<List<DateTranslation>> shifts, BitSet[] giving,
                                  long[] chosen, int date) {
        if (date == chosen.length) {
            for (int i = 0; i < constants.length; i++) {
                if (!statements.get(i).relation().holds(Long.signum(valueAt(weights[i],
                        constants[i], chosen)))) {
                    return false;
                }
            }
            return true;
        }
        for (long year : yearsToLookAt(statements, weights, constants, chosen, date)) {
            if (!giving[date].get(Math.floorMod(year, YEARS_OF_A_CYCLE))
                    || !MonthsAndDaysOfOneDate.coversEveryValueInYear(parts.get(date),
                            (int) year, shifts.get(date))) {
                continue;
            }
            chosen[date] = year;
            if (search(statements, weights, constants, parts, shifts, giving, chosen, date + 1)) {
                return true;
            }
        }
        return false;
    }

    private static long valueAt(long[] weights, long constant, long[] years) {
        long sum = constant;
        for (int date = 0; date < years.length; date++) {
            sum += weights[date] * years[date];
        }
        return sum;
    }

    /**
     * The years for {@code date} that the statements leave, given the dates before it: in the
     * interval they leave, a few at the usual year or the nearest to it, and at each end.
     *
     * <p>The interval is the years of the date at which the statements can hold with some year of
     * the date after it, and not the years at which they hold with the other dates left out: a
     * statement of two dates bounds each by the other, and a second statement fixing the other
     * bounds the first through it. So it does not depend on which date is chosen first. The date
     * after it is eliminated from the statements as they stand over the whole numbers, each
     * statement written as sums that are not below nought.
     */
    private static List<Long> yearsToLookAt(List<Statement> statements, long[][] weights,
                                            long[] constants, long[] chosen, int date) {
        int later = date + 1 < chosen.length ? date + 1 : -1;
        Bounds bounds = new Bounds();
        List<BigInteger[]> lowersOfLater = new ArrayList<>();
        List<BigInteger[]> uppersOfLater = new ArrayList<>();
        for (int i = 0; i < constants.length; i++) {
            BigInteger constant = BigInteger.valueOf(constants[i]);
            for (int before = 0; before < date; before++) {
                constant = constant.add(
                        BigInteger.valueOf(weights[i][before]).multiply(
                                BigInteger.valueOf(chosen[before])));
            }
            for (BigInteger[] sum : notBelowNought(weights[i][date],
                    later < 0 ? 0 : weights[i][later], constant, statements.get(i).relation())) {
                int towardsLater = sum[1].signum();
                if (towardsLater == 0) {
                    bounds.holdAtLeastNought(sum[0], sum[2]);
                } else if (towardsLater > 0) {
                    lowersOfLater.add(sum);
                } else {
                    uppersOfLater.add(sum);
                }
            }
        }
        for (BigInteger[] lower : lowersOfLater) {
            for (BigInteger[] upper : uppersOfLater) {
                // Both are not below nought; the sum that cancels the later date's years is too.
                bounds.holdAtLeastNought(
                        lower[0].multiply(upper[1].negate()).add(upper[0].multiply(lower[1])),
                        lower[2].multiply(upper[1].negate()).add(upper[2].multiply(lower[1])));
            }
        }
        if (bounds.low.compareTo(bounds.high) > 0) {
            return List.of();
        }
        long from = bounds.low.longValueExact();
        long to = bounds.high.longValueExact();
        List<Long> out = new ArrayList<>();
        for (long anchor : new long[] {Math.max(from, Math.min(to, USUAL_YEAR)), from, to}) {
            // A cycle of years from an anchor meets every year of a cycle, so every pattern.
            for (int step = 0; step < YEARS_OF_A_CYCLE; step++) {
                for (long year : new long[] {anchor + step, anchor - step}) {
                    if (from <= year && year <= to && !out.contains(year)) {
                        out.add(year);
                    }
                }
            }
        }
        return out;
    }

    /**
     * The sums, as {@code {a, b, c}} for {@code a * year + b * yearAfter + c}, that are not below
     * nought exactly where {@code wx * year + wz * yearAfter + constant} holds against nought as
     * {@code relation}. Over whole numbers a sum below nought is one at most minus one, so a
     * strict relation loses nothing; a difference from nought says nothing that bounds a year.
     */
    private static List<BigInteger[]> notBelowNought(long wx, long wz, BigInteger constant,
                                                     Rel relation) {
        BigInteger a = BigInteger.valueOf(wx);
        BigInteger b = BigInteger.valueOf(wz);
        BigInteger[] above = {a, b, constant};
        BigInteger[] aboveStrictly = {a, b, constant.subtract(BigInteger.ONE)};
        BigInteger[] below = {a.negate(), b.negate(), constant.negate()};
        BigInteger[] belowStrictly = {a.negate(), b.negate(),
                constant.negate().subtract(BigInteger.ONE)};
        return switch (relation) {
            case GE -> List.<BigInteger[]>of(above);
            case GT -> List.<BigInteger[]>of(aboveStrictly);
            case LE -> List.<BigInteger[]>of(below);
            case LT -> List.<BigInteger[]>of(belowStrictly);
            case EQ -> List.<BigInteger[]>of(above, below);
            case NE -> List.of();
        };
    }

    /** The years of the calendar that sums not below nought leave a date. */
    private static final class Bounds {
        BigInteger low = BigInteger.valueOf(LEAST_YEAR);
        BigInteger high = BigInteger.valueOf(GREATEST_YEAR);

        /** Keeps the years at which {@code a * year + c} is not below nought. */
        void holdAtLeastNought(BigInteger a, BigInteger c) {
            if (a.signum() > 0) {
                low = low.max(ceilingDiv(c.negate(), a));
            } else if (a.signum() < 0) {
                high = high.min(floorDiv(c, a.negate()));
            } else if (c.signum() < 0) {
                high = low.subtract(BigInteger.ONE);
            }
        }
    }

    private static BigInteger floorDiv(BigInteger numerator, BigInteger positive) {
        BigInteger[] divided = numerator.divideAndRemainder(positive);
        return divided[1].signum() < 0 ? divided[0].subtract(BigInteger.ONE) : divided[0];
    }

    private static BigInteger ceilingDiv(BigInteger numerator, BigInteger positive) {
        BigInteger[] divided = numerator.divideAndRemainder(positive);
        return divided[1].signum() > 0 ? divided[0].add(BigInteger.ONE) : divided[0];
    }

    /**
     * Which of the four hundred years of a cycle give every number each part can be. The years
     * before and after repeat them, so this is asked of the calendar once for what was asked, and
     * a year taken is looked at itself.
     */
    private static BitSet classesGivingEveryValue(List<DatesThatStandInEveryYear.Part> parts,
                                                  List<DateTranslation> shifts) {
        return CLASSES.computeIfAbsent(new Asked(List.copyOf(parts), List.copyOf(shifts)),
                asked -> {
                    BitSet out = new BitSet(YEARS_OF_A_CYCLE);
                    for (int at = 0; at < YEARS_OF_A_CYCLE; at++) {
                        if (MonthsAndDaysOfOneDate.coversEveryValueInYear(asked.parts(),
                                (int) USUAL_YEAR + at, asked.yearShifts())) {
                            out.set(Math.floorMod((int) USUAL_YEAR + at, YEARS_OF_A_CYCLE));
                        }
                    }
                    return out;
                });
    }

    /** What was asked of the calendar, which is all there is to the answer. */
    private record Asked(List<DatesThatStandInEveryYear.Part> parts,
                         List<DateTranslation> yearShifts) {}

    /** Answers by what was asked: the same few moves come back across the relations of a
     *  program, and each answer is four hundred years of the calendar. Four hundred bits each. */
    private static final Map<Asked, BitSet> CLASSES = new ConcurrentHashMap<>();

    private static List<DateTranslation> shiftsOf(List<Statement> statements, int date) {
        List<DateTranslation> out = new ArrayList<>();
        for (Statement statement : statements) {
            for (Year year : statement.years()) {
                if (year.date() == date) {
                    out.add(year.moved());
                }
            }
        }
        return out;
    }

    /**
     * Whether every weight and constant is a whole number the type holds, and the weights of a
     * statement, each counted alone and not added, bring it to a number the type holds at the
     * farthest year there is.
     *
     * <p>Counted as exact numbers and each weight alone: the sum of weights is what overflows, and
     * a check of the sum is a check of what the overflow left. A program works the terms of a
     * statement one at a time, and stops where any partial sum passes the type's greatest, and
     * none can where all the terms together at their farthest do not.
     */
    private static boolean staysInsideTheType(List<Statement> statements) {
        BigInteger greatest = BigInteger.valueOf(Long.MAX_VALUE);
        BigInteger farthest = BigInteger.valueOf(Math.max(
                Math.abs(LEAST_YEAR), Math.abs(GREATEST_YEAR)) + YEARS_OF_A_CYCLE);
        for (Statement each : statements) {
            BigInteger constant = wholeOf(each.constant());
            if (constant == null) {
                return false;
            }
            BigInteger size = constant.abs();
            for (Year year : each.years()) {
                BigInteger weight = wholeOf(year.weight());
                if (weight == null) {
                    return false;
                }
                size = size.add(weight.abs().multiply(farthest));
            }
            if (size.compareTo(greatest) > 0) {
                return false;
            }
        }
        return true;
    }

    /** The whole number {@code value} is, or null where it is not one. */
    private static BigInteger wholeOf(ExactRatio value) {
        return value.isWhole() ? value.floor().orNull() : null;
    }

    /** The whole number {@code value} is, which {@link #staysInsideTheType} has shown the type
     *  holds. */
    private static long asLong(ExactRatio value) {
        return wholeOf(value).longValueExact();
    }

    /** The whole number {@code value} is, or null where it is not one or the type does not hold
     *  it. */
    static Long asLongOrNull(ExactRatio value) {
        BigInteger whole = wholeOf(value);
        return whole == null || whole.bitLength() > Long.SIZE - 2 ? null : whole.longValue();
    }
}
