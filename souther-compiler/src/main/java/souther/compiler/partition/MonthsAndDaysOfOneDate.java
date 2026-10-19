package souther.compiler.partition;

import souther.compiler.check.DatePartsLeft;
import souther.compiler.check.HeldClass;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The months and days that go together, for numbers taken of one date that nothing restricts.
 *
 * <p>A month and a day of one date are two numbers, and not every month goes with every day. The
 * combinations are the calendar's, and the calendar repeats every four hundred years, so one cycle
 * of days has them all: a date at either end of the calendar gives a combination some date in the
 * cycle gives as well. A part taken after the date was moved by a number of days is the part of the
 * date that many days on, so it is read at the same day of the cycle.
 *
 * <p>Only for a date no rule restricts. A rule on a part of it, or on the days it may be, leaves
 * the combinations that rule lets through, which this does not read; the caller does not ask.
 */
final class MonthsAndDaysOfOneDate {

    private MonthsAndDaysOfOneDate() {
    }

    /**
     * Every combination of the parts {@code terms} take of one date, in the order of
     * {@code terms}, or null where a term is a part other than a month or a day, or a shift
     * of the date is not defined at every day of the cycle.
     */
    static List<List<ExactRatio>> of(List<NumericTerm.TakenOf> terms) {
        List<TakenAs.DatePart> parts = new ArrayList<>();
        List<DateTranslation> moved = new ArrayList<>();
        for (NumericTerm.TakenOf each : terms) {
            if (!(each.takenAs() instanceof TakenAs.PartOfDate(TakenAs.DatePart part))
                    || part == TakenAs.DatePart.YEAR) {
                return null;
            }
            parts.add(part);
            moved.add(each.transformation().translation());
        }
        Set<List<ExactRatio>> out = new LinkedHashSet<>();
        for (long day = HeldClass.A_CYCLE_STARTS;
                day < HeldClass.A_CYCLE_STARTS + DatePartsLeft.DAYS_OF_A_CYCLE; day++) {
            List<ExactRatio> combination = new ArrayList<>();
            for (int i = 0; i < parts.size(); i++) {
                if (!moved.get(i).definedAt(day)) {
                    return null;
                }
                LocalDate date = LocalDate.ofEpochDay(day + moved.get(i).offsetDays());
                combination.add(ExactRatio.of(parts.get(i) == TakenAs.DatePart.MONTH
                        ? date.getMonthValue() : date.getDayOfMonth()));
            }
            out.add(combination);
        }
        return List.copyOf(out);
    }
}
