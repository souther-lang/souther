package souther.compiler.partition;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.time.Month;
import java.time.YearMonth;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The months and days a date stands at in each kind of year it has.
 *
 * <p>A date at the first of March is in every year, and the month and the day of it moved a day
 * back are the same in all of them. The twenty-ninth of February is not, and neither is a date a
 * shift takes to the other side of the end of its year in some years and not in others. A row at
 * one of the first kind can be put in any year the date has without a part of it changing, so the
 * year is a number nothing said of the month and the day ties.
 *
 * <p>That holds of the years every date of which the date may be. The parts and the years come
 * round with the calendar's cycle of four hundred years, so what is the same in all of those is the
 * same in every year between. The years at either end are another kind: the dates a date may be
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

    private static final int FIRST_YEAR = 2000;
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
     * which every part is the same number in all the years of the cycle and no move puts the date
     * in another year than it is in. At the first and the last year they are the dates of that
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
            List<Origin> alike = alikeOverTheCycle(parts, yearShifts);
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
        return out;
    }

    /**
     * Every month and day at which each of {@code parts} is the same number in all the years of
     * the cycle and no move of {@code yearShifts} puts the date in another year.
     *
     * <p>A question about the calendar's pattern and not about where the moves are defined: it is
     * asked of the years between the first and the last, every date of which every move is
     * defined at, so only what each move moves by is read.
     */
    private static List<Origin> alikeOverTheCycle(List<Part> parts,
                                                  List<DateTranslation> yearShifts) {
        List<Long> partMoves = parts.stream().map(part -> part.moved().offsetDays()).toList();
        List<TakenAs.DatePart> which = parts.stream().map(Part::which).toList();
        List<Long> yearMoves = yearShifts.stream().map(DateTranslation::offsetDays).distinct()
                .sorted().toList();
        return KNOWN.computeIfAbsent(new Asked(which, partMoves, yearMoves),
                asked -> worked(asked.which(), asked.partMoves(), asked.yearMoves()));
    }

    /** What the pattern is asked of, which is all there is to the answer: which parts, and what
     *  each move moves by. */
    private record Asked(List<TakenAs.DatePart> which, List<Long> partMoves,
                         List<Long> yearMoves) {}

    /** Answers by what was asked. A pure function of its key, so an answer is never stale; a
     *  way's statements come back to the same few moves again and again across the relations of
     *  a program, and each answer walks four hundred years of the calendar. */
    private static final Map<Asked, List<Origin>> KNOWN = new ConcurrentHashMap<>();

    private static List<Origin> worked(List<TakenAs.DatePart> which, List<Long> partMoves,
                                       List<Long> yearMoves) {
        List<Origin> out = new ArrayList<>();
        for (int month = 1; month <= 12; month++) {
            for (int day = 1; day <= Month.of(month).maxLength(); day++) {
                int[] taken = alikeEveryYear(month, day, which, partMoves, yearMoves);
                if (taken != null) {
                    out.add(new Origin(month, day, ratiosOf(taken)));
                }
            }
        }
        return out;
    }

    private static int[] alikeEveryYear(int month, int day, List<TakenAs.DatePart> which,
                                        List<Long> partMoves, List<Long> yearMoves) {
        int[] out = null;
        for (int year = FIRST_YEAR; year < FIRST_YEAR + YEARS_OF_A_CYCLE; year++) {
            if (day > YearMonth.of(year, month).lengthOfMonth()) {
                return null;
            }
            long origin = LocalDate.of(year, month, day).toEpochDay();
            for (long move : yearMoves) {
                if (LocalDate.ofEpochDay(origin + move).getYear() != year) {
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
        long from = Math.max(within.first(),
                LocalDate.of(year, 1, 1).toEpochDay() - within.offsetDays());
        long to = Math.min(within.last(),
                LocalDate.of(year, 12, 31).toEpochDay() - within.offsetDays());
        List<Origin> out = new ArrayList<>();
        List<List<ExactRatio>> seen = new ArrayList<>();
        for (long origin = from; origin <= to; origin++) {
            boolean inTheYear = true;
            for (DateTranslation each : yearShifts) {
                inTheYear &= LocalDate.ofEpochDay(origin + each.offsetDays()).getYear() == year;
            }
            if (!inTheYear) {
                continue;
            }
            int[] here = new int[parts.size()];
            for (int i = 0; i < here.length; i++) {
                Part part = parts.get(i);
                here[i] = part.of(LocalDate.ofEpochDay(origin + part.moved().offsetDays()));
            }
            List<ExactRatio> taken = ratiosOf(here);
            if (!seen.contains(taken)) {
                seen.add(taken);
                LocalDate at = LocalDate.ofEpochDay(origin);
                out.add(new Origin(at.getMonthValue(), at.getDayOfMonth(), taken));
            }
        }
        return out;
    }

    private static List<ExactRatio> ratiosOf(int[] numbers) {
        List<ExactRatio> ratios = new ArrayList<>(numbers.length);
        for (int number : numbers) {
            ratios.add(ExactRatio.of(number));
        }
        return List.copyOf(ratios);
    }
}
