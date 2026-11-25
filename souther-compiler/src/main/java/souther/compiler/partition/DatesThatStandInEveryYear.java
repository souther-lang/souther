package souther.compiler.partition;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.LongStream;

/**
 * The months and days a date stands at in each kind of year it has.
 *
 * <p>A date at the first of March is in every year, and the month and the day of it moved a day
 * back are the same in all of them. The twenty-ninth of February is not, and neither is a date a
 * shift takes to the other side of the end of its year in some years and not in others. A row at
 * one of the first kind can be put in any year the date has without a part of it changing, so the
 * year is a number nothing said of the month and the day ties.
 *
 * <p>That holds of the years every date of which the date may be, and is read off those years and
 * no others, as a move is read only at a date it is defined at. The parts and the years come
 * round with the calendar's cycle of four hundred years, so what is the same in a cycle of them is
 * the same in every year between. The years at either end are another kind: the dates a date may be
 * start and stop somewhere, at the calendar's ends or at its own, and so does each move, and a
 * year there holds some of its dates. From the first of January 1900, a date moved a day back is
 * in 1899 on one date only. What a date stands at there is read off the dates of that year it may
 * be, one at a time. The years are each year asked's own, which run over the dates its move is
 * defined at: where a part is defined at fewer dates and leaves a year at an end without one, no
 * kind is told.
 *
 * <p>The dates a date may be are where its moves are defined: each move is told the dates of the
 * date it is taken of before it comes here ({@link DateTranslation#definedOnlyWhere}).
 */
final class DatesThatStandInEveryYear {

    /**
     * The month or the day of a date, taken after the date was moved. The year is not one: it
     * runs as far as the calendar does and goes with no month or day in particular, so it is
     * not a part these are made for.
     */
    record Part(TakenAs.DatePart which, DateTranslation moved) {

        Part {
            if (which == TakenAs.DatePart.YEAR) {
                throw new IllegalArgumentException("the year is not a part that goes with a"
                        + " month and a day");
            }
        }

        /** What this part is of {@code date}. */
        int of(LocalDate date) {
            return which.of(date);
        }

        /** How many numbers this part can be, which are one to that many. */
        int howManyThereAre() {
            if (which == TakenAs.DatePart.YEAR) {
                throw new IllegalStateException("not a part of this kind");
            }
            return which.greatest();
        }

        /** Every number this part can be, as the bits of those numbers. */
        long everyNumber() {
            return (1L << (howManyThereAre() + 1)) - 2;
        }

        /** This part as the cycle of the calendar reads it ({@link PartsOfADateOverACycle}). */
        PartsOfADateOverACycle.Moved overTheCycle() {
            return new PartsOfADateOverACycle.Moved(which, moved.offsetDays());
        }
    }

    /** A month and a day of the date, and the number each of the parts comes to there. */
    record Origin(int month, int day, List<ExactRatio> parts) {}

    private DatesThatStandInEveryYear() {
    }

    /**
     * The months and days the date stands at in each kind of year its year is asked in, with what
     * each of {@code parts} comes to there: one list for the years between the first and the
     * last, each of which holds every date of the year, and one for each of those two — or null
     * where a kind of year has none, or the moves the year is asked after do not give the date
     * one year.
     *
     * <p>The year is the year of the date after the first of {@code yearShifts}, and every other
     * of them is asked to put the date in that year too; where none is given, it is the year of
     * the date itself. Between the first year and the last, the months and days are those at
     * which every part is the same number in all those years and no move puts the date in
     * another year than it is in. At the first and the last year they are the dates of that
     * year at which every move is defined and puts the date in the year.
     *
     * @param parts      the month and day parts taken of the date, each with the move it was
     *                   taken after, defined only where the date may be
     * @param yearShifts the moves of the date whose years are asked, defined the same way
     */
    static List<List<Origin>> byTheYearsOf(List<Part> parts, List<DateTranslation> yearShifts) {
        DateTranslation year = yearShifts.isEmpty() ? DateTranslation.none()
                : yearShifts.getFirst();
        for (DateTranslation each : yearShifts) {
            year = year == null ? null : year.definedOnlyWhere(each);
        }
        for (Part part : parts) {
            year = year == null ? null : year.definedOnlyWhere(part.moved());
        }
        if (year == null) {
            return null;
        }
        int first = year.firstMoved().getYear();
        int last = year.lastMoved().getYear();
        // Each year asked runs over the years of its own move, and a kind of year is told only
        // where those are the years the kinds are told of.
        for (DateTranslation each : yearShifts) {
            if (each.firstMoved().getYear() != first || each.lastMoved().getYear() != last) {
                return null;
            }
        }
        List<List<Origin>> out = new ArrayList<>();
        if (last - first >= 2) {
            List<Origin> alike = alikeInTheYearsBetween(parts, yearShifts, first, last);
            if (alike.isEmpty()) {
                return null;
            }
            out.add(alike);
        }
        for (int end : first == last ? new int[] {first} : new int[] {first, last}) {
            List<Origin> held = heldIn(end, parts, yearShifts, year);
            if (held.isEmpty()) {
                return null;
            }
            out.add(held);
        }
        return List.copyOf(out);
    }

    /**
     * Every month and day at which each of {@code parts} is the same number in all the years
     * between {@code first} and {@code last} and no move of {@code yearShifts} puts the date in
     * another year.
     *
     * <p>Asked of the years strictly between {@code first} and {@code last}, every date of which
     * every move is defined at, and of no other: a move is read only at dates it is defined at.
     * The calendar comes round every four hundred years, so those years are read as the years of
     * the cycle they are ({@link PartsOfADateOverACycle}), all of them where they are a cycle or
     * more.
     */
    static List<Origin> alikeInTheYearsBetween(List<Part> parts, List<DateTranslation> yearShifts,
                                               int first, int last) {
        int cycle = PartsOfADateOverACycle.YEARS_OF_A_CYCLE;
        BitSet between = new BitSet(cycle);
        for (int year = first + 1; year < Math.min(last, first + 1 + cycle); year++) {
            between.set(Math.floorMod(year, cycle));
        }
        // The month and the day of the date itself, then the parts, then the year of the date
        // after each shift: one list for each day.
        List<PartsOfADateOverACycle.Moved> asked = new ArrayList<>();
        asked.add(new PartsOfADateOverACycle.Moved(TakenAs.DatePart.MONTH, 0));
        asked.add(new PartsOfADateOverACycle.Moved(TakenAs.DatePart.DAY, 0));
        parts.forEach(part -> asked.add(part.overTheCycle()));
        yearShifts.forEach(shift -> asked.add(
                new PartsOfADateOverACycle.Moved(TakenAs.DatePart.YEAR, shift.offsetDays())));
        // A month and day is one day of each year, so one list of it given in every year between
        // is the only one given there: the parts are alike in all of them.
        List<Origin> out = new ArrayList<>();
        for (PartsOfADateOverACycle.Given each : PartsOfADateOverACycle.of(asked)) {
            BitSet missing = (BitSet) between.clone();
            missing.andNot(each.years());
            List<Integer> values = each.values();
            if (missing.isEmpty() && values.subList(2 + parts.size(), values.size()).stream()
                    .allMatch(years -> years == 0)) {
                out.add(new Origin(values.get(0), values.get(1), ratiosOf(values
                        .subList(2, 2 + parts.size()).stream().mapToInt(Integer::intValue)
                        .toArray())));
            }
        }
        out.sort(Comparator.comparingInt(Origin::month).thenComparingInt(Origin::day));
        return out;
    }

    /**
     * The months and days of the origins {@code within} is defined at that it puts in
     * {@code year}, every move of {@code yearShifts} putting them there too, with what each of
     * {@code parts} comes to; each list of what the parts come to once.
     */
    private static List<Origin> heldIn(int year, List<Part> parts,
                                       List<DateTranslation> yearShifts, DateTranslation within) {
        DaysOfAYear days = DaysOfAYear.of(year);
        long from = Math.max(within.first(), days.first() - within.offsetDays());
        long to = Math.min(within.last(), days.last() - within.offsetDays());
        // Keyed by what the parts come to, the first origin to come to it kept.
        Map<List<Integer>, Origin> out = new LinkedHashMap<>();
        LongStream.rangeClosed(from, to).forEach(origin -> {
            for (DateTranslation each : yearShifts) {
                if (!days.holds(origin + each.offsetDays())) {
                    return;
                }
            }
            List<Integer> taken = new ArrayList<>(parts.size());
            for (Part part : parts) {
                taken.add(part.of(LocalDate.ofEpochDay(origin + part.moved().offsetDays())));
            }
            out.computeIfAbsent(taken, _ -> {
                LocalDate at = LocalDate.ofEpochDay(origin);
                return new Origin(at.getMonthValue(), at.getDayOfMonth(),
                        ratiosOf(taken.stream().mapToInt(Integer::intValue).toArray()));
            });
        });
        return List.copyOf(out.values());
    }

    /**
     * The days a year runs over, counted from the epoch. Whether a move puts a date in the year is
     * asked of these: a day a move takes a date to is a count, and one past the calendar's ends is
     * in no year of it, where made into a date it would be none.
     */
    record DaysOfAYear(long first, long last) {

        static DaysOfAYear of(int year) {
            return new DaysOfAYear(LocalDate.of(year, 1, 1).toEpochDay(),
                    LocalDate.of(year, 12, 31).toEpochDay());
        }

        boolean holds(long day) {
            return day >= first && day <= last;
        }
    }

    private static List<ExactRatio> ratiosOf(int[] numbers) {
        List<ExactRatio> ratios = new ArrayList<>(numbers.length);
        for (int number : numbers) {
            ratios.add(ExactRatio.of(number));
        }
        return List.copyOf(ratios);
    }
}
