package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Dates are found for statements weighing several parts of them only where the calendar has a
 * date that holds every statement, and each date found is one: worked out here part by part with
 * {@link LocalDate}, and not by what the finder reads.
 */
class DatesAreFoundOnlyWhereTheCalendarHasThemTest {

    private static final DateTranslation EVERY_DATE = DateTranslation.none();

    private static DatesThatHoldEveryStatement.Part year(int date) {
        return new DatesThatHoldEveryStatement.Part(date, TakenAs.DatePart.YEAR, EVERY_DATE);
    }

    private static DatesThatHoldEveryStatement.Part month(int date) {
        return new DatesThatHoldEveryStatement.Part(date, TakenAs.DatePart.MONTH, EVERY_DATE);
    }

    private static DatesThatHoldEveryStatement.Part day(int date) {
        return new DatesThatHoldEveryStatement.Part(date, TakenAs.DatePart.DAY, EVERY_DATE);
    }

    /** {@code weight * part + ... + constant}, held against nought as {@code relation}. */
    private static DatesThatHoldEveryStatement.Statement statement(long constant, Rel relation,
                                                                   Object... weighedParts) {
        Map<DatesThatHoldEveryStatement.Part, Long> parts = new LinkedHashMap<>();
        for (int at = 0; at < weighedParts.length; at += 2) {
            parts.put((DatesThatHoldEveryStatement.Part) weighedParts[at + 1],
                    ((Number) weighedParts[at]).longValue());
        }
        return new DatesThatHoldEveryStatement.Statement(parts, constant, relation);
    }

    /** Whether {@code statements} hold at {@code dates}, each part worked out of its date. */
    private static boolean holdAt(List<DatesThatHoldEveryStatement.Statement> statements,
                                  LocalDate[] dates) {
        for (DatesThatHoldEveryStatement.Statement each : statements) {
            long sum = each.constant();
            for (Map.Entry<DatesThatHoldEveryStatement.Part, Long> part : each.parts().entrySet()) {
                LocalDate moved = dates[part.getKey().date()]
                        .plusDays(part.getKey().moved().offsetDays());
                sum += part.getValue() * part.getKey().which().of(moved);
            }
            if (!each.relation().holds(Long.signum(sum))) {
                return false;
            }
        }
        return true;
    }

    private static LocalDate[] found(List<DateTranslation> days,
                                     DatesThatHoldEveryStatement.Statement... statements) {
        LocalDate[] dates = DatesThatHoldEveryStatement.some(List.of(statements), days);
        if (dates != null) {
            assertTrue(holdAt(List.of(statements), dates), List.of(dates).toString());
            for (int date = 0; date < dates.length; date++) {
                assertTrue(days.get(date).definedAt(dates[date].toEpochDay()),
                        dates[date].toString());
            }
        }
        return dates;
    }

    private static LocalDate[] found(DatesThatHoldEveryStatement.Statement... statements) {
        return found(List.of(EVERY_DATE), statements);
    }

    @Test
    void aYearAndAMonthWeighedTogetherAreFoundInTheMonthTheyComeTo() {
        LocalDate[] dates = found(statement(-200_002, Rel.EQ, 100, year(0), 1, month(0)));

        assertNotNull(dates);
        assertEquals(2000, dates[0].getYear());
        assertEquals(2, dates[0].getMonthValue());
    }

    @Test
    void theThirtiethOfFebruaryIsNoDate() {
        assertNull(found(statement(-2, Rel.EQ, 1, month(0)), statement(-30, Rel.EQ, 1, day(0))));
        assertNull(found(statement(-200_002, Rel.EQ, 100, year(0), 1, month(0)),
                statement(-30, Rel.EQ, 1, day(0))));
    }

    @Test
    void theTwentyNinthOfFebruaryIsADateInALeapYearOnly() {
        assertEquals(LocalDate.of(2000, 2, 29), found(statement(-2000, Rel.EQ, 1, year(0)),
                statement(-2, Rel.EQ, 1, month(0)), statement(-29, Rel.EQ, 1, day(0)))[0]);
        assertNull(found(statement(-1900, Rel.EQ, 1, year(0)),
                statement(-2, Rel.EQ, 1, month(0)), statement(-29, Rel.EQ, 1, day(0))));
    }

    /** {@code month * 100 + day == 229} with the year held to a hundred years from 1900: the
     *  years 1900 and 2100 have none, and the years between have it every four. */
    @Test
    void aMonthAndADayWeighedTogetherAreFoundInAYearThatHasThem() {
        LocalDate[] dates = found(statement(-229, Rel.EQ, 100, month(0), 1, day(0)),
                statement(-1900, Rel.GE, 1, year(0)), statement(-2100, Rel.LE, 1, year(0)));

        assertNotNull(dates);
        assertEquals(LocalDate.of(dates[0].getYear(), 2, 29), dates[0]);
        assertNull(found(statement(-229, Rel.EQ, 100, month(0), 1, day(0)),
                statement(-1900, Rel.EQ, 1, year(0))));
    }

    /** A date the declarations hold from 2000 on has no February of 1900, which a date anywhere
     *  has. */
    @Test
    void aDateIsFoundOnlyAmongTheDatesItMayBe() {
        DateTranslation from2000 = EVERY_DATE.definedOnlyWhere(new DateTranslation(0,
                LocalDate.of(2000, 1, 1).toEpochDay(), LocalDate.MAX.toEpochDay()));
        DatesThatHoldEveryStatement.Statement february1900 =
                statement(-190_002, Rel.EQ, 100, year(0), 1, month(0));

        assertNotNull(found(february1900));
        assertNull(found(List.of(from2000), february1900));
    }

    /** A date the declarations hold to February 2000 is in a year it holds only some days of,
     *  and the date is found among those days. */
    @Test
    void aDateIsFoundInAYearItMayBeOnlySomeDaysOf() {
        DateTranslation february2000 = EVERY_DATE.definedOnlyWhere(new DateTranslation(0,
                LocalDate.of(2000, 2, 1).toEpochDay(), LocalDate.of(2000, 2, 29).toEpochDay()));

        LocalDate[] dates = found(List.of(february2000),
                statement(-200_002, Rel.EQ, 100, year(0), 1, month(0)));

        assertNotNull(dates);
        assertEquals(2, dates[0].getMonthValue());
    }

    /** The year of a date moved a day back is the year before on the first of January: the
     *  move is read where the part is taken, and the date found is the one it moves from. */
    @Test
    void aPartOfAMovedDateIsTakenOfTheDateMoved() {
        DatesThatHoldEveryStatement.Part yearADayBack = new DatesThatHoldEveryStatement.Part(0,
                TakenAs.DatePart.YEAR, EVERY_DATE.thenAddDays(-1));
        LocalDate[] dates = found(statement(-1999, Rel.EQ, 1, yearADayBack),
                statement(-2000, Rel.EQ, 1, year(0)));

        assertNotNull(dates);
        assertEquals(LocalDate.of(2000, 1, 1), dates[0]);
    }

    /** Two dates sixty years apart, the later on the twenty-ninth of February: the earlier is
     *  put sixty years before a leap year. */
    @Test
    void twoDatesAreFoundTogether() {
        LocalDate[] dates = found(List.of(EVERY_DATE, EVERY_DATE),
                statement(-60, Rel.EQ, 1, year(0), -1, year(1)),
                statement(-229, Rel.EQ, 100, month(0), 1, day(0)));

        assertNotNull(dates);
        assertTrue(dates[0].isLeapYear());
    }
}
