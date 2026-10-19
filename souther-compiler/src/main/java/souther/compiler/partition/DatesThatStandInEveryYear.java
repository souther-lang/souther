package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The months and days at which a date stands in every year alike.
 *
 * <p>A date at the first of March is in every year, and the month and the day of it moved a day
 * back are the same in all of them. The twenty-ninth of February is not, and neither is a date a
 * shift takes to the other side of the end of its year in some years and not in others. A row at
 * one of the first kind can be put in any year the date has without a part of it changing, so the
 * year is a number nothing said of the month and the day ties.
 *
 * <p>Only the days up to the twenty-eighth are looked at: a day past it is missing from some
 * month of some year, and one such day more would add nothing the others do not give. The years
 * asked are the four hundred of the calendar's cycle, which repeats, so what holds in all of them
 * holds in every year the calendar has.
 */
final class DatesThatStandInEveryYear {

    private static final int FIRST_YEAR = 2000;
    private static final int YEARS_OF_A_CYCLE = 400;
    private static final int LAST_DAY_IN_EVERY_MONTH = 28;

    private DatesThatStandInEveryYear() {
    }

    /**
     * For each month and day of a date at which it stands in every year alike, the part each of
     * {@code parts} takes of it, or none where there is no such month and day.
     *
     * <p>Alike means that every part is the same number in all the years, and that each of
     * {@code yearShifts} — the moves the years asked of the date are taken after — puts the date
     * in the year it was in. A date that a move takes to another year in some years only, or past
     * the calendar's end, is not one.
     *
     * @param parts      the month and day terms taken of the date, each with the move it was taken
     *                   after
     * @param yearShifts the moves of the date whose years are asked
     */
    static List<Map<NumericTerm.TakenOf, ExactRatio>> of(List<NumericTerm.TakenOf> parts,
                                                         List<DateTranslation> yearShifts) {
        List<Map<NumericTerm.TakenOf, ExactRatio>> out = new ArrayList<>();
        for (int month = 1; month <= 12; month++) {
            for (int day = 1; day <= LAST_DAY_IN_EVERY_MONTH; day++) {
                Map<NumericTerm.TakenOf, ExactRatio> taken = alikeEveryYear(month, day, parts,
                        yearShifts);
                if (taken != null) {
                    out.add(taken);
                }
            }
        }
        return out;
    }

    private static Map<NumericTerm.TakenOf, ExactRatio> alikeEveryYear(
            int month, int day, List<NumericTerm.TakenOf> parts, List<DateTranslation> yearShifts) {
        Map<NumericTerm.TakenOf, ExactRatio> out = new LinkedHashMap<>();
        for (int year = FIRST_YEAR; year < FIRST_YEAR + YEARS_OF_A_CYCLE; year++) {
            long origin = LocalDate.of(year, month, day).toEpochDay();
            for (DateTranslation each : yearShifts) {
                if (!each.definedAt(origin)
                        || LocalDate.ofEpochDay(origin + each.offsetDays()).getYear() != year) {
                    return null;
                }
            }
            for (NumericTerm.TakenOf part : parts) {
                DateTranslation moved = part.transformation().translation();
                if (!moved.definedAt(origin)
                        || !(part.takenAs() instanceof TakenAs.PartOfDate(TakenAs.DatePart which))) {
                    return null;
                }
                LocalDate date = LocalDate.ofEpochDay(origin + moved.offsetDays());
                ExactRatio value = ExactRatio.of(which == TakenAs.DatePart.MONTH
                        ? date.getMonthValue() : date.getDayOfMonth());
                ExactRatio before = out.putIfAbsent(part, value);
                if (before != null && !before.equals(value)) {
                    return null;
                }
            }
        }
        return out;
    }
}
