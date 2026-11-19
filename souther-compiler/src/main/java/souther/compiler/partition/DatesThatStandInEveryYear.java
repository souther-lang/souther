package souther.compiler.partition;

import souther.compiler.check.DatePartsLeft;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.time.Month;
import java.time.YearMonth;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
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

    private static final int YEARS_OF_A_CYCLE = 400;

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

        /**
         * This part with its move less the whole cycles it moves by, at every date: a whole cycle
         * takes a month and a day to the same month and day, so it comes to what this does at
         * every date this is defined at, and is defined at every date of a cycle near the
         * calendar's middle however far this moves. What a part comes to over a cycle is a fact
         * of the calendar and of what the move moves by, and this is that fact's question.
         */
        Part overACycle() {
            return new Part(which, DateTranslation.none().thenAddDays(
                    Math.floorMod(moved.offsetDays(), DatePartsLeft.DAYS_OF_A_CYCLE)));
        }

        /** How many numbers this part can be, which are one to that many. */
        int howManyThereAre() {
            return switch (which) {
                case MONTH -> 12;
                case DAY -> 31;
                case YEAR -> throw new IllegalStateException("not a part of this kind");
            };
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
     * The calendar comes round every four hundred years, so no more than one cycle of them is
     * read, and a whole cycle answers the same wherever it starts.
     */
    private static List<Origin> alikeInTheYearsBetween(List<Part> parts,
                                                       List<DateTranslation> yearShifts,
                                                       int first, int last) {
        List<Long> partMoves = parts.stream().map(part -> part.moved().offsetDays()).toList();
        List<TakenAs.DatePart> which = parts.stream().map(Part::which).toList();
        List<Long> yearMoves = yearShifts.stream().map(DateTranslation::offsetDays).distinct()
                .sorted().toList();
        int from = first + 1;
        int years = Math.min(last - 1, first + YEARS_OF_A_CYCLE) - first;
        int startingIn = years == YEARS_OF_A_CYCLE ? 0 : Math.floorMod(from, YEARS_OF_A_CYCLE);
        return KNOWN.computeIfAbsent(new Asked(which, partMoves, yearMoves, startingIn, years),
                _ -> worked(which, partMoves, yearMoves, from, years));
    }

    /**
     * What the pattern is asked of, which is all there is to the answer: which parts, what each
     * move moves by, and which years of the cycle, as where they start in it and how many there
     * are — a whole cycle starting nowhere in particular.
     */
    private record Asked(List<TakenAs.DatePart> which, List<Long> partMoves,
                         List<Long> yearMoves, int startingIn, int years) {}

    /** Answers by what was asked. A pure function of its key, so an answer is never stale; a
     *  way's statements come back to the same few moves again and again across the relations of
     *  a program, and each answer walks up to four hundred years of the calendar. */
    private static final Map<Asked, List<Origin>> KNOWN = new ConcurrentHashMap<>();

    private static List<Origin> worked(List<TakenAs.DatePart> which, List<Long> partMoves,
                                       List<Long> yearMoves, int from, int years) {
        List<Origin> out = new ArrayList<>();
        for (int month = 1; month <= 12; month++) {
            for (int day = 1; day <= Month.of(month).maxLength(); day++) {
                int[] taken = alikeEveryYear(month, day, which, partMoves, yearMoves, from, years);
                if (taken != null) {
                    out.add(new Origin(month, day, ratiosOf(taken)));
                }
            }
        }
        return out;
    }

    private static int[] alikeEveryYear(int month, int day, List<TakenAs.DatePart> which,
                                        List<Long> partMoves, List<Long> yearMoves, int from,
                                        int years) {
        int[] out = null;
        for (int year = from; year < from + years; year++) {
            if (day > YearMonth.of(year, month).lengthOfMonth()) {
                return null;
            }
            long origin = LocalDate.of(year, month, day).toEpochDay();
            DaysOfAYear days = DaysOfAYear.of(year);
            for (long move : yearMoves) {
                if (!days.holds(origin + move)) {
                    return null;
                }
            }
            int[] here = new int[which.size()];
            for (int i = 0; i < here.length; i++) {
                here[i] = which.get(i).of(LocalDate.ofEpochDay(origin + partMoves.get(i)));
            }
            if (out == null) {
                out = here;
            } else if (!Arrays.equals(out, here)) {
                return null;
            }
        }
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
