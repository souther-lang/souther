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
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Dates are found for statements weighing several parts of them only where the calendar has a
 * date that holds every statement, and each date found is one; and no date is said to hold them
 * only where none does: worked out here part by part with {@link LocalDate}, and not by what the
 * finder reads.
 */
class DatesAreFoundOnlyWhereTheCalendarHasThemTest {

    private static final DateTranslation EVERY_DATE = DateTranslation.none();

    private static final DateTranslation A_DAY_BACK = EVERY_DATE.thenAddDays(-1);

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
                                  List<LocalDate> dates) {
        for (DatesThatHoldEveryStatement.Statement each : statements) {
            long sum = each.constant();
            for (Map.Entry<DatesThatHoldEveryStatement.Part, Long> part : each.parts().entrySet()) {
                LocalDate moved = dates.get(part.getKey().date())
                        .plusDays(part.getKey().moved().offsetDays());
                sum += part.getValue() * part.getKey().which().of(moved);
            }
            if (!each.relation().holds(Long.signum(sum))) {
                return false;
            }
        }
        return true;
    }

    /** What the finder answers, the dates of a {@link DatesThatHoldEveryStatement.Found} checked
     *  against the statements and the dates each may be. */
    private static DatesThatHoldEveryStatement.Answer found(List<DateTranslation> days,
            DatesThatHoldEveryStatement.Statement... statements) {
        DatesThatHoldEveryStatement.Answer answer =
                DatesThatHoldEveryStatement.some(List.of(statements), days);
        if (answer instanceof DatesThatHoldEveryStatement.Found(List<LocalDate> dates)) {
            assertTrue(holdAt(List.of(statements), dates), dates.toString());
            for (int date = 0; date < dates.size(); date++) {
                assertTrue(days.get(date).definedAt(dates.get(date).toEpochDay()),
                        dates.get(date).toString());
            }
        }
        return answer;
    }

    private static DatesThatHoldEveryStatement.Answer found(
            DatesThatHoldEveryStatement.Statement... statements) {
        return found(List.of(EVERY_DATE), statements);
    }

    private static List<LocalDate> dates(DatesThatHoldEveryStatement.Answer answer) {
        return assertInstanceOf(DatesThatHoldEveryStatement.Found.class, answer).dates();
    }

    private static DateTranslation between(LocalDate first, LocalDate last) {
        return EVERY_DATE.definedOnlyWhere(new DateTranslation(0, first.toEpochDay(),
                last.toEpochDay()));
    }

    @Test
    void aYearAndAMonthWeighedTogetherAreFoundInTheMonthTheyComeTo() {
        List<LocalDate> dates = dates(found(statement(-200_002, Rel.EQ, 100, year(0), 1,
                month(0))));

        assertEquals(2000, dates.getFirst().getYear());
        assertEquals(2, dates.getFirst().getMonthValue());
    }

    @Test
    void theThirtiethOfFebruaryIsNoDate() {
        assertEquals(DatesThatHoldEveryStatement.Otherwise.NONE_HOLD,
                found(statement(-2, Rel.EQ, 1, month(0)), statement(-30, Rel.EQ, 1, day(0))));
        assertEquals(DatesThatHoldEveryStatement.Otherwise.NONE_HOLD,
                found(statement(-200_002, Rel.EQ, 100, year(0), 1, month(0)),
                        statement(-30, Rel.EQ, 1, day(0))));
    }

    @Test
    void theTwentyNinthOfFebruaryIsADateInALeapYearOnly() {
        assertEquals(List.of(LocalDate.of(2000, 2, 29)), dates(found(
                statement(-2000, Rel.EQ, 1, year(0)), statement(-2, Rel.EQ, 1, month(0)),
                statement(-29, Rel.EQ, 1, day(0)))));
        assertEquals(DatesThatHoldEveryStatement.Otherwise.NONE_HOLD, found(
                statement(-1900, Rel.EQ, 1, year(0)), statement(-2, Rel.EQ, 1, month(0)),
                statement(-29, Rel.EQ, 1, day(0))));
    }

    /** {@code month * 100 + day == 229} with the year held to a hundred years from 1900: the
     *  years 1900 and 2100 have none, and the years between have it every four. */
    @Test
    void aMonthAndADayWeighedTogetherAreFoundInAYearThatHasThem() {
        LocalDate date = dates(found(statement(-229, Rel.EQ, 100, month(0), 1, day(0)),
                statement(-1900, Rel.GE, 1, year(0)), statement(-2100, Rel.LE, 1, year(0))))
                .getFirst();

        assertEquals(LocalDate.of(date.getYear(), 2, 29), date);
    }

    /** A date the declarations hold from 2000 on has no February of 1900, which a date anywhere
     *  has. */
    @Test
    void aDateIsFoundOnlyAmongTheDatesItMayBe() {
        DateTranslation from2000 = between(LocalDate.of(2000, 1, 1), LocalDate.MAX);
        DatesThatHoldEveryStatement.Statement february1900 =
                statement(-190_002, Rel.EQ, 100, year(0), 1, month(0));

        dates(found(february1900));
        assertEquals(DatesThatHoldEveryStatement.Otherwise.NONE_HOLD,
                found(List.of(from2000), february1900));
    }

    /** A date the declarations hold to February 2000 is in a year it holds only some days of,
     *  and the date is found among those days. */
    @Test
    void aDateIsFoundInAYearItMayBeOnlySomeDaysOf() {
        DateTranslation february2000 = between(LocalDate.of(2000, 2, 1),
                LocalDate.of(2000, 2, 29));

        List<LocalDate> dates = dates(found(List.of(february2000),
                statement(-200_002, Rel.EQ, 100, year(0), 1, month(0))));

        assertEquals(2, dates.getFirst().getMonthValue());
    }

    /** A date the declarations hold to the last day of 2000 and the first months of 2001 has a
     *  March in the later year only, and is found there though the earlier comes first. */
    @Test
    void aDateIsFoundInWhicheverOfItsYearsHasIt() {
        DateTranslation acrossTheNewYear = between(LocalDate.of(2000, 12, 31),
                LocalDate.of(2001, 5, 1));

        dates(found(List.of(acrossTheNewYear), statement(-3, Rel.EQ, 1, month(0))));
    }

    /** A month weighed by a billion billion is past what a whole number holds from October on,
     *  and January, where it is not, is found all the same; where no month it holds at is one,
     *  the months past it are not looked at, and that none holds is not said. */
    @Test
    void aDateIsFoundAmongTheDaysWhoseSumsAWholeNumberHolds() {
        long weight = 1_000_000_000_000_000_000L;

        dates(found(statement(-weight, Rel.EQ, weight, month(0))));
        assertEquals(DatesThatHoldEveryStatement.Otherwise.NOT_SHOWN,
                found(statement(-weight - 1, Rel.EQ, weight, month(0))));
    }

    /** The year of a date moved a day back is the year before on the first of January: the
     *  move is read where the part is taken, and the date found is the one it moves from. */
    @Test
    void aPartOfAMovedDateIsTakenOfTheDateMoved() {
        DatesThatHoldEveryStatement.Part yearADayBack = new DatesThatHoldEveryStatement.Part(0,
                TakenAs.DatePart.YEAR, A_DAY_BACK);

        assertEquals(List.of(LocalDate.of(2000, 1, 1)), dates(found(
                statement(-1999, Rel.EQ, 1, yearADayBack), statement(-2000, Rel.EQ, 1, year(0)))));
    }

    /** Two dates sixty years apart, the later on the twenty-ninth of February: the earlier is
     *  put sixty years before a leap year. */
    @Test
    void twoDatesAreFoundTogether() {
        List<LocalDate> dates = dates(found(List.of(EVERY_DATE, EVERY_DATE),
                statement(-60, Rel.EQ, 1, year(0), -1, year(1)),
                statement(-229, Rel.EQ, 100, month(0), 1, day(0))));

        assertTrue(dates.getFirst().isLeapYear());
    }

    /**
     * {@code 10001 * y == 10000 * x}, stated from above and from below, with x from 3000 to
     * 100000: x = 10001 and y = 10000 hold it, and the search, which looks at some of the years
     * x may be, does not meet a multiple of 10001 there. Not finding them is not that none hold.
     */
    @Test
    void yearsTheSearchDoesNotLookAtAreNotSaidToHoldNothing() {
        DatesThatHoldEveryStatement.Statement[] statements = {
                statement(-3000, Rel.GE, 1, year(0)),
                statement(100_000, Rel.GE, -1, year(0)),
                statement(0, Rel.GE, 10_001, year(1), -10_000, year(0)),
                statement(0, Rel.LE, 10_001, year(1), -10_000, year(0))};
        assertTrue(holdAt(List.of(statements),
                List.of(LocalDate.of(10_001, 1, 1), LocalDate.of(10_000, 1, 1))));

        assertTrue(found(List.of(EVERY_DATE, EVERY_DATE), statements)
                != DatesThatHoldEveryStatement.Otherwise.NONE_HOLD);
    }

    /**
     * The months of a date moved 334 and 335 days on, weighed by four hundred million billion
     * against each other: equal in January of the year after, and in December, where the terms
     * together are past what a whole number holds. The first day of each year with them equal is
     * in January, and moves to December; a day in February holds the statement. A year whose
     * first such day is past it is not one no day of holds it, though it is the only year the
     * date may be.
     */
    @Test
    void aYearWhoseFirstDayOfAKindIsPastAWholeNumberIsNotSaidToHoldNothing() {
        long weight = 400_000_000_000_000_000L;
        DatesThatHoldEveryStatement.Statement equal = statement(0, Rel.EQ,
                weight, new DatesThatHoldEveryStatement.Part(0, TakenAs.DatePart.MONTH,
                        EVERY_DATE.thenAddDays(334)),
                -weight, new DatesThatHoldEveryStatement.Part(0, TakenAs.DatePart.MONTH,
                        EVERY_DATE.thenAddDays(335)));
        assertTrue(holdAt(List.of(equal), List.of(LocalDate.of(2001, 2, 15))));

        assertTrue(found(List.of(between(LocalDate.of(2001, 1, 1), LocalDate.of(2001, 12, 31))),
                equal) != DatesThatHoldEveryStatement.Otherwise.NONE_HOLD);
    }

    /** More dates than the years are chosen together for, or more choices of what their months
     *  and days come to than are looked through: nothing is said. */
    @Test
    void whatTheSearchGivesUpOnIsNotSaid() {
        assertEquals(DatesThatHoldEveryStatement.Otherwise.NOT_SHOWN,
                found(List.of(EVERY_DATE, EVERY_DATE, EVERY_DATE),
                        statement(-2, Rel.EQ, 1, month(0))));
        assertEquals(DatesThatHoldEveryStatement.Otherwise.NOT_SHOWN,
                found(List.of(EVERY_DATE, EVERY_DATE), statement(0, Rel.GE, 100, month(0), 1,
                        day(0), 100, month(1), 1, day(1))));
    }
}
