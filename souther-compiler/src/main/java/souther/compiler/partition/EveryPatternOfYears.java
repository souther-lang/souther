package souther.compiler.partition;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.time.LocalDate;
import java.util.List;

/**
 * Whether a statement of the years of dates holds over a stretch of years that has every pattern
 * of the calendar in it.
 *
 * <p>Whether a year has a twenty-ninth of February, and where a move of some days puts a date
 * among the years, repeat every four hundred years. A statement of the years of several dates that
 * holds at every year of a stretch of two cycles of each, whatever the others are, holds at
 * years of every pattern together, and so leaves the months and days of the dates to be anything
 * the calendar has. A statement that holds at a few years only — one year, or a difference of
 * two years held to one number — does not.
 *
 * <p>The statement is a straight line in the years, so it holds all over a stretch where it holds
 * at the corners of it, the moves of the dates counted as the most they can change a year by. The
 * stretches looked at lie at the ends of the calendar's years, where a statement that holds
 * anywhere that is not near a boundary of its own holds furthest from it.
 */
final class EveryPatternOfYears {

    /** A year of a date, as the weight the statement gives it and the days the date is moved
     *  by before its year is taken. */
    record Year(int date, ExactRatio weight, long offsetDays) {}

    private static final int WIDTH = 800;
    private static final int MARGIN = 1_000;
    private static final long DAYS_IN_A_YEAR = 365;

    private EveryPatternOfYears() {
    }

    /**
     * Whether {@code constant} and the weighed {@code years} come to a number {@code relation}
     * holds nought of, at every choice of a year for each of the {@code dates} inside a stretch of
     * two cycles — in the stretch at one end of the calendar's years or the other, for each date.
     * An equality or a difference from a number is held at no stretch.
     */
    static boolean heldBy(List<Year> years, int dates, ExactRatio constant, Rel relation) {
        if (relation == Rel.EQ || relation == Rel.NE) {
            return false;
        }
        long first = LocalDate.MIN.getYear() + MARGIN;
        long last = LocalDate.MAX.getYear() - MARGIN - WIDTH;
        ExactRatio slack = ExactRatio.ZERO;
        for (Year each : years) {
            long moved = Math.abs(each.offsetDays()) / DAYS_IN_A_YEAR + 2;
            slack = each.weight().abs().times(ExactRatio.of(moved)).flatMap(slack::plus).orNull();
            if (slack == null) {
                return false;
            }
        }
        for (int stretch = 0; stretch < 1 << dates; stretch++) {
            if (heldAtEveryCorner(years, dates, constant, relation, stretch, first, last, slack)) {
                return true;
            }
        }
        return false;
    }

    private static boolean heldAtEveryCorner(List<Year> years, int dates, ExactRatio constant,
                                             Rel relation, int stretch, long first, long last,
                                             ExactRatio slack) {
        for (int corner = 0; corner < 1 << dates; corner++) {
            ExactRatio sum = constant;
            for (Year each : years) {
                long start = (stretch >> each.date() & 1) == 0 ? first : last;
                long year = start + ((corner >> each.date() & 1) == 0 ? 0 : WIDTH - 1);
                sum = sum == null ? null
                        : each.weight().times(ExactRatio.of(year)).flatMap(sum::plus).orNull();
            }
            ExactRatio above = sum == null ? null : sum.plus(slack).orNull();
            ExactRatio below = sum == null ? null : sum.plus(slack.negated()).orNull();
            if (above == null || below == null || !relation.holds(above.signum())
                    || !relation.holds(below.signum())) {
                return false;
            }
        }
        return true;
    }
}
