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
 * <p>The years are found from the statements. Each says between which years a date lies once the
 * other is chosen, and the dates are chosen in turn: a few years in the middle of the interval
 * that is left and at each end of it. The calendar comes in only to say which of those years give
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

    /** The years at which a date can be moved by the moves a statement asks for, with room to
     *  spare at either end of the calendar. */
    private static final long LEAST_YEAR = LocalDate.MIN.getYear() + 1_000L;
    private static final long GREATEST_YEAR = LocalDate.MAX.getYear() - 1_000L;

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
     * <p>The dates after it are free, so only a statement that names no later date bounds it
     * here; the others are held at the end, where every statement is asked.
     */
    private static List<Long> yearsToLookAt(List<Statement> statements, long[][] weights,
                                            long[] constants, long[] chosen, int date) {
        BigInteger low = BigInteger.valueOf(LEAST_YEAR);
        BigInteger high = BigInteger.valueOf(GREATEST_YEAR);
        for (int i = 0; i < constants.length; i++) {
            long weight = weights[i][date];
            boolean namesALaterDate = false;
            for (int later = date + 1; later < chosen.length; later++) {
                namesALaterDate |= weights[i][later] != 0;
            }
            if (weight == 0 || namesALaterDate) {
                continue;
            }
            long constant = constants[i];
            for (int before = 0; before < date; before++) {
                constant += weights[i][before] * chosen[before];
            }
            BigInteger[] interval = intervalOf(weight, constant, statements.get(i).relation());
            if (interval == null) {
                continue;
            }
            low = low.max(interval[0]);
            high = high.min(interval[1]);
        }
        if (low.compareTo(high) > 0) {
            return List.of();
        }
        long from = low.longValueExact();
        long to = high.longValueExact();
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
     * The whole numbers {@code y} at which {@code weight * y + constant}, held against nought as
     * {@code relation}, holds, as the least and the greatest of them — or null where that is no
     * interval: a difference from nought leaves two.
     */
    private static BigInteger[] intervalOf(long weight, long constant, Rel relation) {
        BigInteger w = BigInteger.valueOf(weight);
        BigInteger k = BigInteger.valueOf(-constant);
        Rel asked = relation;
        if (w.signum() < 0) {
            w = w.negate();
            k = k.negate();
            asked = turnedOver(relation);
        }
        BigInteger floor = floorDiv(k, w);
        BigInteger ceiling = ceilingDiv(k, w);
        BigInteger least = BigInteger.valueOf(LEAST_YEAR);
        BigInteger greatest = BigInteger.valueOf(GREATEST_YEAR);
        return switch (asked) {
            case LT -> new BigInteger[] {least, ceiling.subtract(BigInteger.ONE)};
            case LE -> new BigInteger[] {least, floor};
            case GT -> new BigInteger[] {floor.add(BigInteger.ONE), greatest};
            case GE -> new BigInteger[] {ceiling, greatest};
            case EQ -> floor.equals(ceiling) ? new BigInteger[] {floor, floor}
                    : new BigInteger[] {BigInteger.ONE, BigInteger.ZERO};
            case NE -> null;
        };
    }

    /** The relation of the negation: {@code value < 0} is {@code -value > 0}. */
    private static Rel turnedOver(Rel relation) {
        return switch (relation) {
            case LT -> Rel.GT;
            case LE -> Rel.GE;
            case GT -> Rel.LT;
            case GE -> Rel.LE;
            case EQ -> Rel.EQ;
            case NE -> Rel.NE;
        };
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
