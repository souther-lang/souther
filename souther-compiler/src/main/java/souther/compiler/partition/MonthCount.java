package souther.compiler.partition;

import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.CalendarMonths;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.semantics.TakenAs;

import java.math.BigInteger;
import java.time.LocalDate;
import java.time.Year;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The count of the month a date at a place falls in, as a form of the place's numbers: twelve
 * times its year and its month ({@link CalendarMonths#counted}). A move by months stops a run
 * where that count, moved, is past the calendar, and is told as an operation over it
 * ({@link Pullback#monthsToWhereAMoveLands}).
 *
 * <p>Written here and read back here. The form is a sum of two numbers, and a reader that knew
 * the shape apart from the one that writes it could take another sum of a year and a month for it.
 * Read back, it is the place's dates: the months are a run of the dates, so a bound on the count
 * is a bound on the date.
 *
 * <p>And the other form of a date and one of its own parts a run works out on the way to a month:
 * the date less its day of the month, which a move to the first of its month is one more than.
 * What either comes to is read off the date, never off the parts apart ({@link #rangeOf}).
 */
final class MonthCount {

    private MonthCount() {
    }

    /** The count of the month {@code year} and {@code month}, each taken of one date, say, and
     *  {@code more} added. */
    static LinearForm<NumericTerm> of(NumericTerm year, NumericTerm month, BigInteger more) {
        Map<NumericTerm, ExactRatio> weights = new LinkedHashMap<>();
        weights.put(year, ExactRatio.of(CalendarMonths.A_YEAR));
        weights.put(month, ExactRatio.ONE);
        return new LinearForm<>(ExactRatio.of(more), weights);
    }

    /**
     * The place whose dates {@code form} is the count of the month of — or null where it is
     * anything else: twelve times the year and once the month the library takes of one date at a
     * place as it stands, and no constant.
     */
    static TermPath placeCounted(LinearForm<NumericTerm> form) {
        if (form.constant().signum() != 0 || form.coefs().size() != 2) {
            return null;
        }
        TermPath year = null;
        TermPath month = null;
        for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
            if (!(each.getKey() instanceof NumericTerm.TakenOf taken)
                    || !ValueTransformation.NONE.equals(taken.transformation())
                    || !(DefaultBoundOperationFacts.get().takenAs(taken.operation())
                            instanceof TakenAs.PartOfDate(TakenAs.DatePart part))) {
                return null;
            }
            if (part == TakenAs.DatePart.YEAR
                    && each.getValue().equals(ExactRatio.of(CalendarMonths.A_YEAR))) {
                year = taken.position();
            } else if (part == TakenAs.DatePart.MONTH && each.getValue().equals(ExactRatio.ONE)) {
                month = taken.position();
            } else {
                return null;
            }
        }
        return (year != null && year.equals(month)) ? year : null;
    }

    /**
     * The place whose dates {@code form} is each less its own day of the month — the day before
     * the first of its month — or null where it is anything else: the date at a place once, and
     * the day of the month the library takes of it as it stands, taken away, and no constant.
     */
    static TermPath placeAMonthStarts(LinearForm<NumericTerm> form) {
        if (form.constant().signum() != 0 || form.coefs().size() != 2) {
            return null;
        }
        TermPath date = null;
        TermPath day = null;
        for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
            if (each.getKey() instanceof NumericTerm.ValueOf value
                    && each.getValue().equals(ExactRatio.ONE)) {
                date = value.position();
            } else if (each.getKey() instanceof NumericTerm.TakenOf taken
                    && ValueTransformation.NONE.equals(taken.transformation())
                    && DefaultBoundOperationFacts.get().takenAs(taken.operation())
                            instanceof TakenAs.PartOfDate(TakenAs.DatePart part)
                    && part == TakenAs.DatePart.DAY
                    && each.getValue().equals(ExactRatio.ONE.negated())) {
                day = taken.position();
            } else {
                return null;
            }
        }
        return (date != null && date.equals(day)) ? date : null;
    }

    /**
     * The numbers {@code form} comes to where it is one of the dates at one place and its parts,
     * and a constant: the count of the month of the date ({@link #placeCounted}), or the date less
     * its own day of the month ({@link #placeAMonthStarts}). Each is what it comes to at the least
     * and the greatest date the place holds, as its type and the rules over it say, since it runs
     * with the date. Null where it is neither, or the place has no end on either side.
     *
     * <p>The parts are numbers of one date, so the form is no sum of what each comes to apart: a
     * place held to the end of November of the last year holds no date whose year is the last and
     * whose month is December, and the first day of the calendar is no date whose day of the
     * month is two.
     */
    static FormRange rangeOf(LinearForm<NumericTerm> form, InputReading read) {
        if (form == null) {
            return null;
        }
        LinearForm<NumericTerm> bare = new LinearForm<>(ExactRatio.ZERO, form.coefs());
        TermPath counted = placeCounted(bare);
        TermPath dates = counted != null ? counted : placeAMonthStarts(bare);
        FormRange days = dates == null ? null
                : FormRange.endsHeldByTheRules(new NumericTerm.ValueOf(dates), read);
        BigInteger shift = wholeOf(form.constant());
        if (days == null || shift == null) {
            return null;
        }
        BigInteger least = counted != null ? countOf(days.least()) : dayBeforeItsMonth(days.least());
        BigInteger greatest = counted != null ? countOf(days.greatest())
                : dayBeforeItsMonth(days.greatest());
        return (least == null || greatest == null) ? null
                : new FormRange(ExactRatio.of(least.add(shift)),
                        ExactRatio.of(greatest.add(shift)));
    }

    /** The day before the first of the month the day {@code epochDay} falls in, or null where it
     *  is no day of the calendar. */
    private static BigInteger dayBeforeItsMonth(ExactRatio epochDay) {
        BigInteger day = dayOfTheCalendar(epochDay);
        return day == null ? null : BigInteger.valueOf(
                LocalDate.ofEpochDay(day.longValue()).withDayOfMonth(1).toEpochDay() - 1);
    }

    /** The count of the month the day {@code epochDay} falls in, or null where it is no day of
     *  the calendar. */
    private static BigInteger countOf(ExactRatio epochDay) {
        BigInteger day = dayOfTheCalendar(epochDay);
        return day == null ? null
                : BigInteger.valueOf(countOf(LocalDate.ofEpochDay(day.longValue())));
    }

    /** {@code epochDay} where it is a day of the calendar, and null otherwise. */
    private static BigInteger dayOfTheCalendar(ExactRatio epochDay) {
        BigInteger day = wholeOf(epochDay);
        return (day == null || day.compareTo(BigInteger.valueOf(LocalDate.MIN.toEpochDay())) < 0
                || day.compareTo(BigInteger.valueOf(LocalDate.MAX.toEpochDay())) > 0) ? null : day;
    }

    /** {@code number} where it is whole, and null otherwise. */
    private static BigInteger wholeOf(ExactRatio number) {
        return number != null && number.isWhole()
                && number.truncated() instanceof ExactAnswer.Held<BigInteger> whole
                ? whole.value() : null;
    }

    /**
     * The days of the dates whose month is counted from {@code least} to {@code greatest}, either
     * null where nothing bounds it there: from the first day of the month counted {@code least}
     * to the last of the one counted {@code greatest}, each null where it asks nothing of a date —
     * an end on the far side of the calendar. Null where no date is counted between them.
     */
    static BigInteger[] daysWithin(BigInteger least, BigInteger greatest) {
        BigInteger first = BigInteger.valueOf(countOf(LocalDate.MIN));
        BigInteger last = BigInteger.valueOf(countOf(LocalDate.MAX));
        if ((least != null && least.compareTo(last) > 0)
                || (greatest != null && greatest.compareTo(first) < 0)
                || (least != null && greatest != null && least.compareTo(greatest) > 0)) {
            return null;
        }
        BigInteger from = (least == null || least.compareTo(first) <= 0) ? null
                : BigInteger.valueOf(CalendarMonths.counted(least.longValueExact()).atDay(1)
                        .toEpochDay());
        BigInteger to = (greatest == null || greatest.compareTo(last) >= 0) ? null
                : BigInteger.valueOf(CalendarMonths.counted(greatest.longValueExact())
                        .atEndOfMonth().toEpochDay());
        return new BigInteger[] {from, to};
    }

    /**
     * The months from the first month of year nought to the calendar's first, and to its last:
     * where a move by months, counted so, stops a run past either.
     */
    static BigInteger[] monthsHeld() {
        BigInteger aYear = BigInteger.valueOf(CalendarMonths.A_YEAR);
        return new BigInteger[] {BigInteger.valueOf(Year.MIN_VALUE).multiply(aYear),
                BigInteger.valueOf(Year.MAX_VALUE).multiply(aYear).add(aYear)
                        .subtract(BigInteger.ONE)};
    }

    /**
     * The counts of the months whose first day, moved by {@code days}, is a day of the calendar:
     * the least and the greatest — or null where no month's is. The first days run with the
     * counts, so those are a run of the counts.
     */
    static BigInteger[] countsWhoseFirstDayMoves(long days) {
        long first = LocalDate.MIN.toEpochDay();
        long last = LocalDate.MAX.toEpochDay();
        long earliest;
        long latest;
        try {
            earliest = Math.subtractExact(first, days);
            latest = Math.subtractExact(last, days);
        } catch (ArithmeticException _) {
            return null;
        }
        if (latest < first || earliest > last) {
            return null;
        }
        LocalDate from = LocalDate.ofEpochDay(Math.max(earliest, first));
        long least = (from.getDayOfMonth() == 1 || earliest < first) ? countOf(from)
                : countOf(from) + 1;
        long greatest = countOf(LocalDate.ofEpochDay(Math.min(latest, last)));
        return least > greatest ? null
                : new BigInteger[] {BigInteger.valueOf(least), BigInteger.valueOf(greatest)};
    }

    /** The count of the month {@code date} falls in. */
    private static long countOf(LocalDate date) {
        return date.getYear() * (long) CalendarMonths.A_YEAR + date.getMonthValue();
    }
}
