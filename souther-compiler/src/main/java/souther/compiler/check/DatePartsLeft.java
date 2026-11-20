package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.TakenAs;

import java.math.BigInteger;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * Where the rules of a value leave each part of the date standing at one of its positions.
 *
 * <p>What a range on the date cannot say. {@code Date.day(value) == 1} leaves the first of every
 * month, and the dates between two of them are dates of the order that no value of the position is.
 * Read as the ends of the date alone, the rule says nothing, and a search choosing a date would
 * offer the fifteenth.
 *
 * <p>Of the date as it stands. A part of the date a day later is a part of another date, and what it
 * leaves this one is a walk over the days, not a part of this one.
 *
 * <p>Walked over the days and not solved over the parts, because the parts constrain each other: how
 * far the days of a month run turns on the month, and February's on the year. Every day walked is a
 * day the calendar has, so no date is offered that the calendar does not have, and none it has is
 * missed for want of a part nobody spoke of.
 *
 * @param byPart the range each part the rules spoke of is left in. A part they said nothing of is
 *               absent, and runs as far as the calendar has it
 * @param yearsLeave what the year leaves by each divisor the rules spoke of: the remainders it may
 *                   leave. A divisor they said nothing of is absent
 */
public record DatePartsLeft(Map<TakenAs.DatePart, NumericDomain.Bounds> byPart,
                            Map<Integer, Set<Integer>> yearsLeave) {

    /** The days of one cycle of the Gregorian calendar, which repeats every four hundred years: a
     *  walk of the parts of a date that went this far has met every combination of them there is.
     *  The remainders a year leaves repeat in no cycle of this length unless their divisors divide
     *  four hundred ({@link #cyclesBeforeTheClassRepeats}). */
    public static final long DAYS_OF_A_CYCLE = 146_097;

    /** The years of one cycle of the calendar. */
    private static final int YEARS_OF_A_CYCLE = 400;

    /** How many cycles of the calendar a walk goes without meeting a day before it says it stopped
     *  short, where the cycle of the class it walks is more than that: ten thousand years, in each
     *  of which a walk takes at most a step for the year and one for each month. */
    static final int MOST_CYCLES_WALKED = 25;

    /** The first and last days the calendar has. */
    public static final long FIRST_DAY = LocalDate.MIN.toEpochDay();
    public static final long LAST_DAY = LocalDate.MAX.toEpochDay();

    public DatePartsLeft {
        if (byPart.isEmpty() && yearsLeave.isEmpty()) {
            throw new IllegalArgumentException("a date nothing was said of the parts of leaves"
                    + " every date, which is no class of them");
        }
        byPart = Collections.unmodifiableMap(new EnumMap<>(
                byPart.isEmpty() ? new EnumMap<>(TakenAs.DatePart.class) : byPart));
        Map<Integer, Set<Integer>> copied = new TreeMap<>();
        yearsLeave.forEach((divisor, remainders) -> {
            if (divisor <= 0) {
                throw new IllegalArgumentException("a year leaves a remainder by a divisor above"
                        + " nought: " + divisor);
            }
            copied.put(divisor, Set.copyOf(remainders));
        });
        yearsLeave = Collections.unmodifiableMap(copied);
    }

    /** What the rules leave of the parts of a date, where they said nothing of the year's
     *  remainders. */
    public DatePartsLeft(Map<TakenAs.DatePart, NumericDomain.Bounds> byPart) {
        this(byPart, Map.of());
    }

    /** The date whose year leaves one of {@code remainders} by {@code divisor}. */
    public static DatePartsLeft yearLeaving(int divisor, Set<Integer> remainders) {
        return new DatePartsLeft(Map.of(), Map.of(divisor, remainders));
    }

    /**
     * The days met walking from one day towards another, and whether the walk stopped with days
     * still unwalked that may hold more.
     */
    public record Walked(List<Long> days, boolean leftSome) {

        public Walked {
            days = List.copyOf(days);
        }
    }

    /** The parts both of these leave: each part met with what the other leaves it. */
    public DatePartsLeft and(DatePartsLeft other) {
        Map<TakenAs.DatePart, NumericDomain.Bounds> both = new EnumMap<>(TakenAs.DatePart.class);
        both.putAll(byPart);
        other.byPart.forEach((part, bounds) -> both.merge(part, bounds, NumericDomain.Bounds::meet));
        Map<Integer, Set<Integer>> remainders = new TreeMap<>(yearsLeave);
        other.yearsLeave.forEach((divisor, left) -> remainders.merge(divisor, left, (one, two) -> {
            Set<Integer> shared = new TreeSet<>(one);
            shared.retainAll(two);
            return shared;
        }));
        return new DatePartsLeft(both, remainders);
    }

    /** Whether {@code part} is left at {@code value}. */
    public boolean leaves(TakenAs.DatePart part, int value) {
        NumericDomain.Bounds left = byPart.get(part);
        if (left != null && !left.admits(ExactRatio.of(value))) {
            return false;
        }
        if (part != TakenAs.DatePart.YEAR) {
            return true;
        }
        for (Map.Entry<Integer, Set<Integer>> each : yearsLeave.entrySet()) {
            if (!each.getValue().contains(Math.floorMod(value, each.getKey()))) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether a date these leave has {@code part} at {@code value}, shown by a day the walk met.
     * A walk that stopped with days unwalked shows none and says nothing of whether there are
     * some, so false here is that this shows no such date and never that there is none.
     */
    public boolean someDateHas(TakenAs.DatePart part, int value) {
        Endpoint at = Endpoint.inclusive(Count.of(value));
        return !and(new DatePartsLeft(Map.of(part, new NumericDomain.Bounds(at, at))))
                .walk(null, null, true, 1).days().isEmpty();
    }

    /** Whether the date {@code day} counts to has parts these leave. */
    public boolean holds(long day) {
        if (day < FIRST_DAY || day > LAST_DAY) {
            return false;
        }
        LocalDate date = LocalDate.ofEpochDay(day);
        return leaves(TakenAs.DatePart.YEAR, TakenAs.DatePart.YEAR.of(date))
                && leaves(TakenAs.DatePart.MONTH, TakenAs.DatePart.MONTH.of(date))
                && leaves(TakenAs.DatePart.DAY, TakenAs.DatePart.DAY.of(date));
    }

    /**
     * How many cycles of the calendar the parts these leave repeat in: the years the calendar
     * repeats in and each divisor the year is held to divide a whole number of them, and the days
     * these leave at one day they leave at the day that many cycles on.
     */
    BigInteger cyclesBeforeTheClassRepeats() {
        BigInteger years = BigInteger.valueOf(YEARS_OF_A_CYCLE);
        for (int divisor : yearsLeave.keySet()) {
            BigInteger by = BigInteger.valueOf(divisor);
            years = years.multiply(by).divide(years.gcd(by));
        }
        return years.divide(BigInteger.valueOf(YEARS_OF_A_CYCLE));
    }

    /** Whether some date the calendar has may have parts these leave: not where a walk over them
     *  met none and went as far as there is. */
    public boolean leaveADate() {
        if (yearsLeave.values().stream().anyMatch(Set::isEmpty)) {
            return false;
        }
        Walked first = walk(null, null, true, 1);
        return !first.days().isEmpty() || first.leftSome();
    }

    /**
     * The days these hold met walking from {@code from} towards {@code to}, at most {@code most} of
     * them: a day at a time, and a month at a time past a month or a year these do not leave.
     *
     * <p>Over the days the run, the calendar and the years these leave have in common, and nothing
     * where they have none. A run reaching past the calendar holds no day there, and cut to the
     * calendar end by end it would name the calendar's last day for a run that lies wholly after it.
     * The years first, since a year is the one part that does not come round again. Past that, a walk
     * that went a whole cycle of the class beyond the last day it met has met every combination of
     * the parts there is ({@link #cyclesBeforeTheClassRepeats}), so it ends there and says it left
     * none. A class whose cycle is more than {@link #MOST_CYCLES_WALKED} cycles of the calendar is
     * walked no further than that, and says it left some, for the days past it are not met.
     *
     * @param from the day the walk starts at, or null for the calendar's end on that side
     * @param to   the day it goes no further than, or null for the calendar's end on that side
     */
    public Walked walk(BigInteger from, BigInteger to, boolean upward, int most) {
        BigInteger low = upward ? from : to;
        BigInteger high = upward ? to : from;
        BigInteger firstHeld = BigInteger.valueOf(FIRST_DAY);
        BigInteger lastHeld = BigInteger.valueOf(LAST_DAY);
        NumericDomain.Bounds years = byPart.get(TakenAs.DatePart.YEAR);
        if (years != null && years.min() != null && wholeYear(years, true) instanceof Long first) {
            firstHeld = BigInteger.valueOf(LocalDate.of(first.intValue(), 1, 1).toEpochDay());
        }
        if (years != null && years.max() != null && wholeYear(years, false) instanceof Long last) {
            lastHeld = BigInteger.valueOf(LocalDate.of(last.intValue(), 12, 31).toEpochDay());
        }
        BigInteger lowest = low == null ? firstHeld : low.max(firstHeld);
        BigInteger highest = high == null ? lastHeld : high.min(lastHeld);
        List<Long> out = new ArrayList<>();
        if (lowest.compareTo(highest) > 0) {
            return new Walked(out, false);
        }
        BigInteger cycles = cyclesBeforeTheClassRepeats();
        boolean wholeClass = cycles.compareTo(BigInteger.valueOf(MOST_CYCLES_WALKED)) <= 0;
        long unmetToTheEnd = DAYS_OF_A_CYCLE * (wholeClass ? cycles.longValueExact()
                : MOST_CYCLES_WALKED);
        long end = (upward ? highest : lowest).longValueExact();
        long unmet = 0;
        long day = (upward ? lowest : highest).longValueExact();
        while (upward ? day <= end : day >= end) {
            if (out.size() >= most) {
                return new Walked(out, true);
            }
            LocalDate date = LocalDate.ofEpochDay(day);
            int year = TakenAs.DatePart.YEAR.of(date);
            long next;
            if (!leaves(TakenAs.DatePart.YEAR, year)) {
                // Nothing of this year is held, so the walk goes to the first day of the next one,
                // or the last day of the one before. The last year the calendar has has no next.
                next = !upward ? LocalDate.of(year, 1, 1).toEpochDay() - 1
                        : year == LocalDate.MAX.getYear() ? LAST_DAY + 1
                        : LocalDate.of(year + 1, 1, 1).toEpochDay();
            } else if (!leaves(TakenAs.DatePart.MONTH, TakenAs.DatePart.MONTH.of(date))) {
                // Nothing of this month is held, so the walk goes to the first day of the next one,
                // or the last day of the one before. The last month the calendar has has no next.
                next = !upward ? date.withDayOfMonth(1).toEpochDay() - 1
                        : TakenAs.DatePart.YEAR.of(date) == LocalDate.MAX.getYear()
                                && TakenAs.DatePart.MONTH.of(date) == 12 ? LAST_DAY + 1
                        : date.withDayOfMonth(1).plusMonths(1).toEpochDay();
            } else {
                if (leaves(TakenAs.DatePart.DAY, TakenAs.DatePart.DAY.of(date))) {
                    out.add(day);
                    unmet = 0;
                }
                next = upward ? day + 1 : day - 1;
            }
            unmet += Math.abs(next - day);
            if (unmet > unmetToTheEnd) {
                return new Walked(out, !wholeClass);
            }
            day = next;
        }
        return new Walked(out, false);
    }

    /** The nearest year an end of {@code years} admits, inside the calendar, or null where the end
     *  names no number this reads. */
    private static Long wholeYear(NumericDomain.Bounds years, boolean lower) {
        BigInteger whole = (lower ? years.min() : years.max()).wholeAdmitted(lower);
        if (whole == null) {
            return null;
        }
        return whole.max(BigInteger.valueOf(LocalDate.MIN.getYear()))
                .min(BigInteger.valueOf(LocalDate.MAX.getYear())).longValueExact();
    }
}
