package souther.compiler.partition;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.time.Month;
import java.time.YearMonth;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.IntStream;

/**
 * The months and days at which a date stands in every year alike.
 *
 * <p>A date at the first of March is in every year, and the month and the day of it moved a day
 * back are the same in all of them. The twenty-ninth of February is not, and neither is a date a
 * shift takes to the other side of the end of its year in some years and not in others. A row at
 * one of the first kind can be put in any year the date has without a part of it changing, so the
 * year is a number nothing said of the month and the day ties.
 *
 * <p>A day that some month of some year does not have is not such a date, and the thirty-first of
 * January is one. The parts and the years come round with the calendar's cycle of four hundred
 * years, so what is the same in all of them is the same in every year between. But the calendar
 * has a first and a last year, and a shift is defined at the dates between its first and its last
 * origin only, so the two years at the ends are looked at as well: a month and a day a shift
 * takes out of the calendar there is a date some year does not have.
 */
final class DatesThatStandInEveryYear {

    private static final int FIRST_YEAR = 2000;
    private static final int YEARS_OF_A_CYCLE = 400;

    /** The years of the cycle, and the first and the last year the calendar has. */
    private static final int[] YEARS_ASKED = IntStream.concat(
            IntStream.range(FIRST_YEAR, FIRST_YEAR + YEARS_OF_A_CYCLE),
            IntStream.of(LocalDate.MIN.getYear(), LocalDate.MAX.getYear())).toArray();

    /** A part of a date, taken after the date was moved. */
    record Part(TakenAs.DatePart which, DateTranslation moved) {}

    /** A month and a day of the date, and the number each of the parts comes to there. */
    record Origin(int month, int day, List<ExactRatio> parts) {}

    private DatesThatStandInEveryYear() {
    }

    /**
     * Every month and day of a date at which it stands in every year alike, with what each of
     * {@code parts} comes to there.
     *
     * <p>Alike means that every part is the same number in all the years, that each of
     * {@code yearShifts} — the moves the years asked of the date are taken after — puts the date
     * in the year it was in, and that every move is defined at the date in each year, those at
     * the ends of the calendar included.
     *
     * @param parts      the month and day parts taken of the date, each with the move it was
     *                   taken after
     * @param yearShifts the moves of the date whose years are asked
     */
    static List<Origin> of(List<Part> parts, List<DateTranslation> yearShifts) {
        return KNOWN.computeIfAbsent(new Asked(List.copyOf(parts), List.copyOf(yearShifts)),
                asked -> worked(asked.parts(), asked.yearShifts()));
    }

    /** What was asked, which is all there is to the answer: the calendar and the moves. */
    private record Asked(List<Part> parts, List<DateTranslation> yearShifts) {}

    /** Answers by what was asked. A pure function of its key, so an answer is never stale; a
     *  way's statements come back to the same few moves again and again across the relations of
     *  a program, and each answer walks four hundred years of the calendar. */
    private static final Map<Asked, List<Origin>> KNOWN = new ConcurrentHashMap<>();

    private static List<Origin> worked(List<Part> parts, List<DateTranslation> yearShifts) {
        List<Origin> out = new ArrayList<>();
        for (int month = 1; month <= 12; month++) {
            for (int day = 1; day <= Month.of(month).maxLength(); day++) {
                List<ExactRatio> taken = alikeEveryYear(month, day, parts, yearShifts);
                if (taken != null) {
                    out.add(new Origin(month, day, taken));
                }
            }
        }
        return out;
    }

    private static List<ExactRatio> alikeEveryYear(int month, int day, List<Part> parts,
                                                   List<DateTranslation> yearShifts) {
        List<ExactRatio> out = null;
        for (int year : YEARS_ASKED) {
            if (day > YearMonth.of(year, month).lengthOfMonth()) {
                return null;
            }
            long origin = LocalDate.of(year, month, day).toEpochDay();
            for (DateTranslation each : yearShifts) {
                if (!each.definedAt(origin)
                        || LocalDate.ofEpochDay(origin + each.offsetDays()).getYear() != year) {
                    return null;
                }
            }
            List<ExactRatio> here = new ArrayList<>();
            for (Part part : parts) {
                if (!part.moved().definedAt(origin)) {
                    return null;
                }
                LocalDate date = LocalDate.ofEpochDay(origin + part.moved().offsetDays());
                here.add(ExactRatio.of(part.which() == TakenAs.DatePart.MONTH
                        ? date.getMonthValue() : date.getDayOfMonth()));
            }
            if (out == null) {
                out = here;
            } else if (!out.equals(here)) {
                return null;
            }
        }
        return out;
    }
}
