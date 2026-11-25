package souther.compiler.partition;

import souther.compiler.check.DatePartsLeft;
import souther.compiler.check.RuleOfDateParts;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;

import java.math.BigInteger;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Whether some date the declarations leave has a part among some values, once moved: one
 * question, asked of everything the declarations say of the date at once.
 *
 * <p>They say three things of it: the days between its ends, the range each part is left
 * ({@link DatePartsLeft}), and what the parts are held to together ({@link RuleOfDateParts}).
 * Each of them can leave a date with the part while no date is left by all of them. Under
 * {@code Date.day(value) - Date.month(value) >= 28} February is a month the calendar has and a
 * month between the ends the rule leaves the month, and no date of February holds the rule. So a
 * date is shown only where one date is of all three.
 *
 * <p>Where the declarations hold no two parts together, the class is walked for the part, which
 * is what the question costs where there is no rule of two parts. Otherwise the part is held to
 * the values asked by statements beside the rules, and the dates holding all of them are looked
 * for in the class ({@link DatesThatHoldEveryStatement}).
 */
final class DatesTheDeclarationsLeave {

    private DatesTheDeclarationsLeave() {
    }

    /**
     * A date of {@code left} between the ends {@code days} says, holding every one of
     * {@code rules}, whose part {@code part}, once moved as {@code moved} moves it, is a value of
     * {@code asked} — or that there is none, or neither shown.
     *
     * <p>Each run of {@code asked} is asked whole: the value of a run nearest the line may be one
     * no date has while another is. None hold only where none hold in every run, and a run whose
     * ends name no number is not shown.
     *
     * @param days the dates the declarations leave the date by its ends, as the days a move by
     *             nothing is defined at
     */
    static DatesThatHoldEveryStatement.Answer withThePartIn(DatePartsLeft left,
                                                            List<RuleOfDateParts> rules,
                                                            DateTranslation days,
                                                            TakenAs.DatePart part,
                                                            LevelRegion asked,
                                                            DateTranslation moved) {
        boolean noneHold = true;
        for (LevelInterval run : asked.parts()) {
            LevelInterval.WholeNumbers whole = run.wholeNumbers();
            DatesThatHoldEveryStatement.Answer answer = whole == null
                    ? DatesThatHoldEveryStatement.Otherwise.NOT_SHOWN
                    : withThePartIn(left, rules, days, part, whole.least(), whole.most(), moved);
            if (answer instanceof DatesThatHoldEveryStatement.Found) {
                return answer;
            }
            noneHold &= answer == DatesThatHoldEveryStatement.Otherwise.NONE_HOLD;
        }
        return noneHold ? DatesThatHoldEveryStatement.Otherwise.NONE_HOLD
                : DatesThatHoldEveryStatement.Otherwise.NOT_SHOWN;
    }

    /** The same, of the part from {@code least} to {@code most}, both counted, where null is no
     *  end: held to what the part comes to on the calendar first. */
    private static DatesThatHoldEveryStatement.Answer withThePartIn(
            DatePartsLeft left, List<RuleOfDateParts> rules, DateTranslation days,
            TakenAs.DatePart part, BigInteger least, BigInteger most, DateTranslation moved) {
        int[] calendar = {part.least(), part.greatest()};
        int from = least == null ? calendar[0]
                : least.max(BigInteger.valueOf(calendar[0])).min(BigInteger.valueOf(calendar[1]
                        + 1L)).intValueExact();
        int to = most == null ? calendar[1]
                : most.min(BigInteger.valueOf(calendar[1])).max(BigInteger.valueOf(calendar[0]
                        - 1L)).intValueExact();
        if (from > to) {
            return DatesThatHoldEveryStatement.Otherwise.NONE_HOLD;
        }
        if (rules.isEmpty()) {
            DateTranslation within = moved.definedOnlyWhere(days);
            LocalDate found = within == null ? null : left.aDateWithin(part, from, to, within);
            return found == null ? DatesThatHoldEveryStatement.Otherwise.NOT_SHOWN
                    : new DatesThatHoldEveryStatement.Found(List.of(found));
        }
        List<DatesThatHoldEveryStatement.Statement> statements = new ArrayList<>();
        for (RuleOfDateParts rule : rules) {
            Map<DatesThatHoldEveryStatement.Part, Long> parts = new LinkedHashMap<>();
            for (Map.Entry<TakenAs.DatePart, ExactRatio> each : rule.weights().entrySet()) {
                Long weight = YearsAWayAllows.asLongOrNull(each.getValue());
                if (weight == null) {
                    return DatesThatHoldEveryStatement.Otherwise.NOT_SHOWN;
                }
                parts.put(new DatesThatHoldEveryStatement.Part(0, each.getKey(),
                        DateTranslation.none()), weight);
            }
            Long constant = YearsAWayAllows.asLongOrNull(rule.constant());
            if (constant == null) {
                return DatesThatHoldEveryStatement.Otherwise.NOT_SHOWN;
            }
            statements.add(new DatesThatHoldEveryStatement.Statement(parts, constant,
                    rule.relation()));
        }
        Map<DatesThatHoldEveryStatement.Part, Long> theAsked =
                Map.of(new DatesThatHoldEveryStatement.Part(0, part, moved), 1L);
        if (from == to) {
            statements.add(new DatesThatHoldEveryStatement.Statement(theAsked, -(long) from,
                    Rel.EQ));
        } else {
            statements.add(new DatesThatHoldEveryStatement.Statement(theAsked, -(long) from,
                    Rel.GE));
            statements.add(new DatesThatHoldEveryStatement.Statement(theAsked, -(long) to,
                    Rel.LE));
        }
        return DatesThatHoldEveryStatement.some(statements, List.of(days), List.of(left));
    }
}
