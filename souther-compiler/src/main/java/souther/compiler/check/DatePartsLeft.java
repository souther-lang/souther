package souther.compiler.check;

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
 */
public record DatePartsLeft(Map<TakenAs.DatePart, NumericDomain.Bounds> byPart) {

    /** The days of one cycle of the Gregorian calendar, which repeats every four hundred years: a
     *  walk that went this far and met no date has met every combination of parts there is. */
    private static final long DAYS_OF_A_CYCLE = 146_097;

    /** The first and last days the calendar has. */
    public static final long FIRST_DAY = LocalDate.MIN.toEpochDay();
    public static final long LAST_DAY = LocalDate.MAX.toEpochDay();

    public DatePartsLeft {
        if (byPart.isEmpty()) {
            throw new IllegalArgumentException("a date nothing was said of the parts of leaves"
                    + " every date, which is no class of them");
        }
        byPart = Collections.unmodifiableMap(new EnumMap<>(byPart));
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
        return new DatePartsLeft(both);
    }

    /** Whether {@code part} is left at {@code value}. */
    public boolean leaves(TakenAs.DatePart part, int value) {
        NumericDomain.Bounds left = byPart.get(part);
        return left == null || left.admits(ExactRatio.of(value));
    }

    /** Whether the date {@code day} counts to has parts these leave. */
    public boolean holds(long day) {
        if (day < FIRST_DAY || day > LAST_DAY) {
            return false;
        }
        LocalDate date = LocalDate.ofEpochDay(day);
        return leaves(TakenAs.DatePart.YEAR, date.getYear())
                && leaves(TakenAs.DatePart.MONTH, date.getMonthValue())
                && leaves(TakenAs.DatePart.DAY, date.getDayOfMonth());
    }

    /** Whether some date the calendar has has parts these leave. */
    public boolean leaveADate() {
        return !walk(null, null, true, 1).days().isEmpty();
    }

    /**
     * The days these hold met walking from {@code from} towards {@code to}, at most {@code most} of
     * them: a day at a time, and a month at a time past a month or a year these do not leave.
     *
     * <p>Over the days the run, the calendar and the years these leave have in common, and nothing
     * where they have none. A run reaching past the calendar holds no day there, and cut to the
     * calendar end by end it would name the calendar's last day for a run that lies wholly after it.
     * The years first, since a year is the one part that does not come round again. Past that, a walk
     * that went a whole cycle of the calendar beyond the last day it met has met every combination
     * of a month and a day there is, so it ends there and says it left none.
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
        long end = (upward ? highest : lowest).longValueExact();
        long unmet = 0;
        long day = (upward ? lowest : highest).longValueExact();
        while (upward ? day <= end : day >= end) {
            if (out.size() >= most) {
                return new Walked(out, true);
            }
            LocalDate date = LocalDate.ofEpochDay(day);
            long next;
            if (!leaves(TakenAs.DatePart.YEAR, date.getYear())
                    || !leaves(TakenAs.DatePart.MONTH, date.getMonthValue())) {
                // Nothing of this month is held, so the walk goes to the first day of the next one,
                // or the last day of the one before. The last month the calendar has has no next.
                next = !upward ? date.withDayOfMonth(1).toEpochDay() - 1
                        : date.getYear() == LocalDate.MAX.getYear()
                                && date.getMonthValue() == 12 ? LAST_DAY + 1
                        : date.withDayOfMonth(1).plusMonths(1).toEpochDay();
            } else {
                if (leaves(TakenAs.DatePart.DAY, date.getDayOfMonth())) {
                    out.add(day);
                    unmet = 0;
                }
                next = upward ? day + 1 : day - 1;
            }
            unmet += Math.abs(next - day);
            if (unmet > DAYS_OF_A_CYCLE) {
                return new Walked(out, false);
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
