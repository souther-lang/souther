package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
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
 * The days a year's remainders and the parts of a date leave repeat every
 * lcm(400, the divisors) years and not every four hundred, so a walk that met none in four hundred
 * years has not met every combination unless the divisors divide four hundred. Where the cycle is
 * more years than a walk goes, it says some may be left.
 */
class WhatTheYearLeavesIsACycleOfItsOwnTest {

    private static long day(int year, int month, int dayOfMonth) {
        return LocalDate.of(year, month, dayOfMonth).toEpochDay();
    }

    private static DatePartsLeft ofTheLeapDay(int divisor, int remainder) {
        Endpoint february = Endpoint.inclusive(Count.of(2));
        Endpoint twentyNinth = Endpoint.inclusive(Count.of(29));
        return DatePartsLeft.yearLeaving(divisor, Set.of(remainder)).and(new DatePartsLeft(Map.of(
                TakenAs.DatePart.MONTH, new NumericDomain.Bounds(february, february),
                TakenAs.DatePart.DAY, new NumericDomain.Bounds(twentyNinth, twentyNinth))));
    }

    @Test
    void aLeapDayInAYearThatIsAMultipleOf399IsMetAtTheEndOfAWalkLongerThanFourHundredYears() {
        DatePartsLeft left = ofTheLeapDay(399, 0);
        assertTrue(left.holds(day(3192, 2, 29)));
        DatePartsLeft.Walked walked = left.walk(BigInteger.valueOf(day(1994, 1, 1)), null, true, 1);
        assertEquals(List.of(day(3192, 2, 29)), walked.days());
        assertTrue(left.leaveADate());
    }

    @Test
    void aClassWhoseCycleIsLongerThanAWalkGoesSaysSomeMayBeLeft() {
        // A year that is 2 by 396 is 2 by 4, which no leap year is; the cycle is 39,600 years, more
        // than a walk goes, so the walk cannot say there is none.
        DatePartsLeft left = ofTheLeapDay(396, 2);
        DatePartsLeft.Walked walked = left.walk(BigInteger.valueOf(day(1994, 1, 1)), null, true, 1);
        assertTrue(walked.days().isEmpty());
        assertTrue(walked.leftSome(), "the walk stopped short of the cycle");
        assertTrue(left.leaveADate(), "a date that may stand is not a date that none does");
    }

    @Test
    void aDivisorOfFourHundredLeavesAWalkOfFourHundredYearsTheWholeOfIt() {
        // 2 is a year's remainder by 100 that no leap year leaves, and 400 years show it.
        DatePartsLeft left = ofTheLeapDay(100, 50);
        DatePartsLeft.Walked walked = left.walk(BigInteger.valueOf(day(1994, 1, 1)), null, true, 1);
        assertTrue(walked.days().isEmpty());
        assertFalse(walked.leftSome(), "four hundred years is every combination there is");
        assertFalse(left.leaveADate());
    }
}
