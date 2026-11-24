package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a date moved by months comes to is what exactly one of the cases of the move says, over the
 * numbers of the date it is moved from: for every date, whichever months it is moved by, the cases
 * that hold of it are one, and the number that case answers is the one the runtime's move gives.
 *
 * <p>Over the dates of the years round the ones that tell the leap years apart: year nought, a
 * century that is not leap and one that is. The cases are built from what a year leaves by four,
 * a hundred and four hundred, which these years take every value of that matters.
 */
class ADateMovedByMonthsIsOneOfTheCasesItIsReadInTest {

    /** The numbers of a date, as a case states and answers them. */
    private static long numberOf(MonthMoveCases.Of of, LocalDate date) {
        return switch (of) {
            case DAY_NUMBER -> date.toEpochDay();
            case YEAR -> date.getYear();
            case MONTH -> date.getMonthValue();
            case DAY_OF_MONTH -> date.getDayOfMonth();
            case YEAR_BY_4 -> Math.floorMod(date.getYear(), 4);
            case YEAR_BY_100 -> Math.floorMod(date.getYear(), 100);
            case YEAR_BY_400 -> Math.floorMod(date.getYear(), 400);
        };
    }

    /** The cases that hold of {@code date}. */
    private static List<MonthMoveCases.Case> holdingOf(List<MonthMoveCases.Case> cases,
                                                        LocalDate date) {
        List<MonthMoveCases.Case> out = new ArrayList<>();
        for (MonthMoveCases.Case each : cases) {
            if (each.given().stream().allMatch(stand -> stand.holds(numberOf(stand.of(), date)))) {
                out.add(each);
            }
        }
        return out;
    }

    private static long answeredAt(MonthMoveCases.Case one, LocalDate date) {
        long answer = one.constant();
        for (Map.Entry<MonthMoveCases.Of, Long> weight : one.weights().entrySet()) {
            answer += weight.getValue() * numberOf(weight.getKey(), date);
        }
        return answer;
    }

    /** The years that tell the leap years apart: nought, where a year's remainders are taken of a
     *  year that is not above nought, a century that is not leap and one that is. A move reaches
     *  two years either side, so three each side leaves every year it lands in a neighbour. */
    private static final int[] AROUND = {0, 1900, 2000};

    private static List<LocalDate> datesRoundTheLeapYears(boolean onlyTheFirst) {
        List<LocalDate> out = new ArrayList<>();
        for (int around : AROUND) {
            for (int year = around - 3; year <= around + 3; year++) {
                addTheDatesOf(year, onlyTheFirst, out);
            }
        }
        return out;
    }

    private static void addTheDatesOf(int year, boolean onlyTheFirst, List<LocalDate> out) {
        for (int month = 1; month <= 12; month++) {
            LocalDate first = LocalDate.of(year, month, 1);
            for (int day = 1; day <= first.lengthOfMonth(); day++) {
                // The days a month's length and its neighbours' make a difference at.
                if (onlyTheFirst ? day == 1 : day == 1 || day >= 27 || day == 15) {
                    out.add(first.withDayOfMonth(day));
                }
            }
        }
    }

    /** One case holds of each date, and what it answers is where the runtime lands the date, for
     *  the day count and the day of the month and the year of the date moved. */
    @Test
    void eachDateIsInOneCaseAndItsAnswerIsTheRuntimes() {
        List<LocalDate> dates = datesRoundTheLeapYears(false);
        for (long months = -MonthMoveCases.MOST_MONTHS; months <= MonthMoveCases.MOST_MONTHS;
                months++) {
            for (MonthMoveCases.Asked asked : MonthMoveCases.Asked.values()) {
                List<MonthMoveCases.Case> cases = MonthMoveCases.of(months, asked, false);
                for (LocalDate date : dates) {
                    LocalDate landed = CalendarMonths.movedBy(months, date);
                    List<MonthMoveCases.Case> holding = holdingOf(cases, date);
                    String where = asked + " of " + date + " moved by " + months;
                    assertEquals(1, holding.size(), where);
                    long expected = switch (asked) {
                        case DAY_NUMBER -> landed.toEpochDay();
                        case DAY_OF_MONTH -> landed.getDayOfMonth();
                        case YEAR -> landed.getYear();
                        case MONTH -> landed.getMonthValue();
                    };
                    assertEquals(expected, answeredAt(holding.getFirst(), date), where);
                }
            }
        }
    }

    /** Of the first of a month, no case is of a day past the end of the month it lands in, and
     *  none states the day: the cases are fewer and each still holds of exactly the dates it
     *  does, answering what the runtime does. */
    @Test
    void theFirstOfAMonthIsInOneCaseThatStatesNoDay() {
        List<LocalDate> dates = datesRoundTheLeapYears(true);
        for (long months = -MonthMoveCases.MOST_MONTHS; months <= MonthMoveCases.MOST_MONTHS;
                months++) {
            for (MonthMoveCases.Asked asked : MonthMoveCases.Asked.values()) {
                List<MonthMoveCases.Case> cases = MonthMoveCases.of(months, asked, true);
                assertTrue(cases.stream().noneMatch(one -> one.given().stream()
                                .anyMatch(stand -> stand.of() == MonthMoveCases.Of.DAY_OF_MONTH)),
                        asked + " by " + months);
                assertTrue(cases.stream().noneMatch(one -> one.weights()
                                .containsKey(MonthMoveCases.Of.DAY_OF_MONTH)),
                        asked + " by " + months);
                for (LocalDate date : dates) {
                    LocalDate landed = CalendarMonths.movedBy(months, date);
                    List<MonthMoveCases.Case> holding = holdingOf(cases, date);
                    String where = asked + " of " + date + " moved by " + months;
                    assertEquals(1, holding.size(), where);
                    long expected = switch (asked) {
                        case DAY_NUMBER -> landed.toEpochDay();
                        case DAY_OF_MONTH -> landed.getDayOfMonth();
                        case YEAR -> landed.getYear();
                        case MONTH -> landed.getMonthValue();
                    };
                    assertEquals(expected, answeredAt(holding.getFirst(), date), where);
                }
            }
        }
    }

    /** A move by more months than are read in cases is none. */
    @Test
    void aMoveByManyMonthsIsReadInNoCases() {
        assertNull(MonthMoveCases.of(MonthMoveCases.MOST_MONTHS + 1,
                MonthMoveCases.Asked.DAY_NUMBER, false));
        assertNull(MonthMoveCases.of(-MonthMoveCases.MOST_MONTHS - 1,
                MonthMoveCases.Asked.YEAR, false));
    }

    /** The cases a move by one month is read in are few: the months, the years that tell the
     *  length of February apart, and the days past the end of a shorter month. */
    @Test
    void aMoveByOneMonthIsReadInAFewCases() {
        assertEquals(2, MonthMoveCases.of(1, MonthMoveCases.Asked.YEAR, false).size());
        assertEquals(12 + 3, MonthMoveCases.of(1, MonthMoveCases.Asked.DAY_NUMBER, true).size());
    }
}
