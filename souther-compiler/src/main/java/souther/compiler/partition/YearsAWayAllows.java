package souther.compiler.partition;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;

import java.math.BigInteger;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

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

    private static final int YEARS_OF_A_CYCLE = PartsOfADateOverACycle.YEARS_OF_A_CYCLE;

    /** The first and the last year the calendar has. A move defined at fewer dates is asked of a
     *  year when it is chosen, not by leaving the ends out here. */
    private static final long LEAST_YEAR = LocalDate.MIN.getYear();
    private static final long GREATEST_YEAR = LocalDate.MAX.getYear();

    /** The year the middle of the calendar's use is taken to be, which is where a year is looked
     *  for first. */
    private static final long USUAL_YEAR = 2_000;

    /** The dates a way may state the years of for them to be chosen together: the years of one
     *  are looked for among those of the other, so the choices multiply. */
    static final int MOST_DATES = 2;

    private YearsAWayAllows() {
    }

    /**
     * A year for each date, in the order of {@code partsOfEachDate}, at which every statement holds
     * and in which each date gives every number each of its parts can be — or null where none is
     * found.
     *
     * <p>A date's days in a year are those at which no move a statement takes its year after
     * puts the date in another year. The statements are then about that year, whatever the day.
     * A date is put only in a year every day of which each of its moves is defined at, so that the
     * days of the year are dates it may be.
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
        List<List<DateTranslation>> shifts = new ArrayList<>();
        List<int[]> wholeYears = new ArrayList<>();
        for (int date = 0; date < dates; date++) {
            shifts.add(shiftsOf(statements, date));
            DateTranslation every = DateTranslation.none();
            for (DateTranslation each : shifts.get(date)) {
                every = every == null ? null : every.definedOnlyWhere(each);
            }
            for (DatesThatStandInEveryYear.Part part : partsOfEachDate.get(date)) {
                every = every == null ? null : every.definedOnlyWhere(part.moved());
            }
            int[] whole = every == null ? null : every.wholeYears();
            if (whole == null) {
                return null;
            }
            wholeYears.add(whole);
        }
        BitSet[] giving = new BitSet[dates];
        for (int date = 0; date < dates; date++) {
            giving[date] = classesGivingEveryValue(partsOfEachDate.get(date), shifts.get(date));
            if (giving[date].isEmpty()) {
                return null;   // no year gives this date every number, whatever the statements
            }
        }
        return years(statements, (date, year) ->
                giving[date].get(Math.floorMod(year, YEARS_OF_A_CYCLE))
                        && MonthsAndDaysOfOneDate.coversEveryValueInYear(
                                partsOfEachDate.get(date), (int) year, shifts.get(date)),
                wholeYears, YearsAWayAllows::toInts);
    }

    /**
     * What {@code made} makes of the first years it makes anything of, among those, one for each
     * date, at which every statement holds, each year one of a cycle of four hundred
     * {@code ofTheCycle} sets for its date and inside the years {@code allowed} gives it — or null
     * where it makes nothing of any. What the year of a moved date is beside the date's own year
     * is the caller's to have put in the constants: every {@link Year#moved} here is read as moving
     * nothing.
     *
     * <p>The years of the cycle are where some day gives what the caller asks of the date, which a
     * year only some days of which the date may be need not have among them: so whether the years
     * are taken is what {@code made} makes of them, and the search goes on past those it makes
     * nothing of.
     *
     * @param ofTheCycle for each date, the years of a cycle, by the year modulo four hundred
     * @param allowed    for each date, its first and last year
     * @param made       what the caller makes of the years, or null where it makes nothing
     */
    static <T> T holding(List<Statement> statements, List<BitSet> ofTheCycle,
                         List<int[]> allowed, Function<long[], T> made) {
        int dates = ofTheCycle.size();
        if (dates == 0 || dates > MOST_DATES || allowed.size() != dates
                || !staysInsideTheType(statements)) {
            return null;
        }
        return years(statements, (date, year) ->
                ofTheCycle.get(date).get(Math.floorMod(year, YEARS_OF_A_CYCLE)), allowed, made);
    }

    /** Whether a year is one a date may be put in, before the statements are asked of it. */
    @FunctionalInterface
    private interface Taken {
        boolean at(int date, long year);
    }

    /** What {@code made} makes of the first years it makes anything of, among those the
     *  statements, which stay inside the type, hold at, each one {@code taken} allows — or null
     *  where none is found. */
    private static <T> T years(List<Statement> statements, Taken taken, List<int[]> allowed,
                               Function<long[], T> made) {
        int dates = allowed.size();
        long[][] weights = new long[statements.size()][dates];
        long[] constants = new long[statements.size()];
        for (int i = 0; i < constants.length; i++) {
            constants[i] = asLong(statements.get(i).constant());
            for (Year year : statements.get(i).years()) {
                // Cannot pass the type: every weight was counted alone against the farthest year.
                weights[i][year.date()] += asLong(year.weight());
            }
        }
        return search(statements, weights, constants, taken, allowed, made, new long[dates], 0);
    }

    private static int[] toInts(long[] years) {
        int[] out = new int[years.length];
        for (int i = 0; i < out.length; i++) {
            out[i] = (int) years[i];
        }
        return out;
    }

    /**
     * What {@code made} makes of the first years, the dates from {@code date} on put in them, that
     * hold every statement with those already chosen and that it makes anything of — or null.
     */
    private static <T> T search(List<Statement> statements, long[][] weights, long[] constants,
                                Taken taken, List<int[]> allowed, Function<long[], T> made,
                                long[] chosen, int date) {
        if (date == chosen.length) {
            for (int i = 0; i < constants.length; i++) {
                if (!statements.get(i).relation().holds(Long.signum(valueAt(weights[i],
                        constants[i], chosen)))) {
                    return null;
                }
            }
            return made.apply(chosen);
        }
        for (long year : yearsToLookAt(statements, weights, constants, chosen, date,
                allowed.get(date))) {
            if (!taken.at(date, year)) {
                continue;
            }
            chosen[date] = year;
            T found = search(statements, weights, constants, taken, allowed, made, chosen,
                    date + 1);
            if (found != null) {
                return found;
            }
        }
        return null;
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
                                            long[] constants, long[] chosen, int date,
                                            int[] allowed) {
        int later = date + 1 < chosen.length ? date + 1 : -1;
        Bounds bounds = new Bounds();
        bounds.low = bounds.low.max(BigInteger.valueOf(allowed[0]));
        bounds.high = bounds.high.min(BigInteger.valueOf(allowed[1]));
        List<BigInteger[]> lowersOfLater = new ArrayList<>();
        List<BigInteger[]> uppersOfLater = new ArrayList<>();
        Lattice lattice = Lattice.EVERY_YEAR;
        for (int i = 0; i < constants.length; i++) {
            BigInteger constant = BigInteger.valueOf(constants[i]);
            for (int before = 0; before < date; before++) {
                constant = constant.add(
                        BigInteger.valueOf(weights[i][before]).multiply(
                                BigInteger.valueOf(chosen[before])));
            }
            if (later >= 0 && statements.get(i).relation() == Rel.EQ
                    && weights[i][date] != 0 && weights[i][later] != 0
                    && lattice == Lattice.EVERY_YEAR) {
                lattice = Lattice.of(BigInteger.valueOf(weights[i][date]),
                        BigInteger.valueOf(weights[i][later]), constant);
                if (lattice == null) {
                    return List.of();
                }
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
        Set<Long> out = new LinkedHashSet<>();
        for (long anchor : new long[] {Math.max(from, Math.min(to, USUAL_YEAR)), from, to}) {
            BigInteger onTheLattice = lattice.atOrBelow(BigInteger.valueOf(anchor));
            // The years the lattice allows come round in the calendar's pattern within a cycle of
            // them, because a step of the lattice moves the year and the one it goes with by the
            // same amounts every time: so a cycle of them from an anchor meets every pattern.
            for (int step = 0; step < YEARS_OF_A_CYCLE; step++) {
                BigInteger moved = lattice.modulus().multiply(BigInteger.valueOf(step));
                for (BigInteger candidate : new BigInteger[] {
                        onTheLattice.add(moved), onTheLattice.subtract(moved)}) {
                    if (bounds.low.compareTo(candidate) <= 0
                            && candidate.compareTo(bounds.high) <= 0) {
                        out.add(candidate.longValueExact());
                    }
                }
            }
        }
        return List.copyOf(out);
    }

    /**
     * The years of a date at which a statement of two dates held to nought, {@code a * year +
     * b * yearAfter + c = 0}, can hold at all: those congruent to {@code residue} modulo
     * {@code modulus}, because the year after is then the whole number the statement gives.
     * Looking at the years in a row would meet none of them where the weights are large, whatever
     * the interval.
     */
    private record Lattice(BigInteger residue, BigInteger modulus) {

        static final Lattice EVERY_YEAR = new Lattice(BigInteger.ZERO, BigInteger.ONE);

        /** The lattice of {@code a * x + b * z + c = 0}, or null where no whole x and z hold it. */
        static Lattice of(BigInteger a, BigInteger b, BigInteger c) {
            BigInteger gcd = a.gcd(b);
            if (c.remainder(gcd).signum() != 0) {
                return null;
            }
            BigInteger reducedA = a.divide(gcd);
            BigInteger modulus = b.abs().divide(gcd);
            BigInteger residue = c.divide(gcd).negate()
                    .multiply(reducedA.modInverse(modulus)).mod(modulus);
            return new Lattice(residue, modulus);
        }

        /** The greatest year on the lattice that is not past {@code year}. */
        BigInteger atOrBelow(BigInteger year) {
            return year.subtract(year.subtract(residue).mod(modulus));
        }
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
     * Which of the four hundred years of a cycle give every number each part can be, at the days
     * every shift keeps in the year ({@link MonthsAndDaysOfOneDate#coversEveryValueInYear}). The
     * years before and after repeat them, so this is read off the cycle
     * ({@link PartsOfADateOverACycle}), and a year taken is looked at itself.
     *
     * <p>The calendar's pattern and nothing else: each move is asked by what it moves by, and the
     * dates it is defined at are asked of the year taken. A shift is read as the year of the date
     * it moves, which keeps the date in its year where it is nought.
     */
    static BitSet classesGivingEveryValue(List<DatesThatStandInEveryYear.Part> parts,
                                          List<DateTranslation> shifts) {
        List<PartsOfADateOverACycle.Moved> asked = new ArrayList<>();
        for (DatesThatStandInEveryYear.Part part : parts) {
            asked.add(new PartsOfADateOverACycle.Moved(part.which(), part.moved().offsetDays()));
        }
        for (DateTranslation shift : shifts) {
            asked.add(new PartsOfADateOverACycle.Moved(TakenAs.DatePart.YEAR,
                    shift.offsetDays()));
        }
        // What the parts give, by the years that give it: the lists of one day are in the same
        // years as many others, and a year is asked once for each set of years.
        Map<BitSet, long[]> seenIn = new LinkedHashMap<>();
        for (PartsOfADateOverACycle.Given each : PartsOfADateOverACycle.of(asked)) {
            if (each.values().subList(parts.size(), asked.size()).stream()
                    .anyMatch(years -> years != 0)) {
                continue;
            }
            long[] seen = seenIn.computeIfAbsent(each.years(), _ -> new long[parts.size()]);
            for (int i = 0; i < seen.length; i++) {
                seen[i] |= 1L << each.values().get(i);
            }
        }
        BitSet out = new BitSet(YEARS_OF_A_CYCLE);
        for (int year = 0; year < YEARS_OF_A_CYCLE; year++) {
            long[] seen = new long[parts.size()];
            boolean kept = false;
            for (Map.Entry<BitSet, long[]> each : seenIn.entrySet()) {
                if (each.getKey().get(year)) {
                    kept = true;
                    for (int i = 0; i < seen.length; i++) {
                        seen[i] |= each.getValue()[i];
                    }
                }
            }
            boolean every = kept;
            for (int i = 0; i < seen.length; i++) {
                every &= seen[i] == parts.get(i).everyNumber();
            }
            if (every) {
                out.set(year);
            }
        }
        return out;
    }

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
