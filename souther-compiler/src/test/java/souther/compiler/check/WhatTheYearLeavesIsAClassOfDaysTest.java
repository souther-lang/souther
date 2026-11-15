package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Count;
import souther.compiler.semantics.TakenAs;

import java.math.BigInteger;
import java.time.LocalDate;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The days whose year leaves a remainder are a class of days, met with the parts of a date the
 * rules also fix: a day is of it where its year leaves one of the remainders and every part is
 * where the rules leave it, and the walk of the days meets only those.
 */
class WhatTheYearLeavesIsAClassOfDaysTest {

    private static long day(int year, int month, int dayOfMonth) {
        return LocalDate.of(year, month, dayOfMonth).toEpochDay();
    }

    @Test
    void aDayIsOfTheClassWhereItsYearLeavesOneOfTheRemaindersAndItsMonthIsWhereTheRulesLeaveIt() {
        Endpoint february = Endpoint.inclusive(Count.of(2));
        DatePartsLeft leap = DatePartsLeft.yearLeaving(4, Set.of(0)).and(new DatePartsLeft(
                Map.of(TakenAs.DatePart.MONTH, new NumericDomain.Bounds(february, february))));
        assertTrue(leap.holds(day(2024, 2, 29)));
        assertFalse(leap.holds(day(2025, 2, 10)), "a year leaving one by four");
        assertFalse(leap.holds(day(2024, 3, 1)), "a month the rules do not leave");
    }

    @Test
    void theWalkMeetsOnlyDaysOfTheClass() {
        DatePartsLeft leap = DatePartsLeft.yearLeaving(4, Set.of(0));
        DatePartsLeft.Walked walked = leap.walk(BigInteger.valueOf(day(2025, 1, 1)), null, true, 2);
        assertEquals(List.of(day(2028, 1, 1), day(2028, 1, 2)), walked.days());
    }
}
