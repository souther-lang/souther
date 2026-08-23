package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A divide rounded to a scale lies between the two points of that scale's grid the exact quotient
 * lies between, and the ends are those points and not the exact quotient moved a step.
 *
 * <p>The difference is at nought and it is the whole reason to write it this way. A quotient at or
 * above nought lands on a grid point at or above nought whatever the scale is, and the same range
 * moved one step down starts below it — so a construction owing {@code value >= 0} would come out
 * owed for the width of a step of a scale nobody asked about.
 *
 * <p>Which way the call rounds is not read. Every mode the library has picks one of the two points,
 * so the pair holds all seven.
 */
class AQuotientRoundedToAScaleLandsOnThatScalesGridTest {

    private static NumericDomain.Bounds between(String low, String high) {
        return new NumericDomain.Bounds(
                low == null ? null : Endpoint.inclusive(new Count(new BigDecimal(low))),
                high == null ? null : Endpoint.inclusive(new Count(new BigDecimal(high))));
    }

    private static NumericDomain.Bounds at(String n) {
        return between(n, n);
    }

    private static String low(NumericDomain.Bounds b) {
        return b.min() == null ? null : Count.number(b.min().at()).at().toPlainString();
    }

    private static String high(NumericDomain.Bounds b) {
        return b.max() == null ? null : Count.number(b.max().at()).at().toPlainString();
    }

    /** A quotient no decimal writes is held between the grid points either side of it. Ten over
     * three is 3.333…, which at two places lies between 3.33 and 3.34. */
    @Test
    void aQuotientNoDecimalWritesIsHeldBetweenTheGridPointsEitherSide() {
        NumericDomain.Bounds q = Intervals.roundedQuotient(at("10"), at("3"), 2);
        assertEquals("3.33", low(q));
        assertEquals("3.34", high(q));
    }

    /** One that lands on the grid is that point at both ends. */
    @Test
    void aQuotientOnTheGridIsThatPoint() {
        NumericDomain.Bounds q = Intervals.roundedQuotient(at("10"), at("4"), 2);
        assertEquals("2.50", low(q));
        assertEquals("2.50", high(q));
    }

    /** The ends are the grid's, so a range at or above nought stays there — which a step down would
     * not. At scale nought, everything under one floors to nought. */
    @Test
    void aQuotientAtOrAboveNoughtStaysThere() {
        NumericDomain.Bounds q = Intervals.roundedQuotient(between("0", "5"), at("100"), 0);
        assertEquals("0", low(q));
        assertEquals("1", high(q));
    }

    /** And below nought the same way round. */
    @Test
    void aQuotientAtOrBelowNoughtStaysThere() {
        NumericDomain.Bounds q = Intervals.roundedQuotient(between("-5", "0"), at("100"), 0);
        assertEquals("-1", low(q));
        assertEquals("0", high(q));
    }

    /** A coarse scale is a coarse grid, and the ends are still that grid's. Two places to the left
     * of the point holds 3.33… between nought and a hundred. */
    @Test
    void aScaleLeftOfThePointIsACoarserGrid() {
        NumericDomain.Bounds q = Intervals.roundedQuotient(at("10"), at("3"), -2);
        assertEquals("0", low(q));
        assertEquals("100", high(q));
    }

    /** The corners, over a range of dividends and a range of divisors held off nought. */
    @Test
    void theHullIsTakenOverTheCorners() {
        NumericDomain.Bounds q = Intervals.roundedQuotient(between("-10", "10"), between("2", "5"), 1);
        assertEquals("-5.0", low(q));
        assertEquals("5.0", high(q));
    }

    /** A divisor running past every value sends the quotient toward nought, and the grid point it
     * is rounded outward to on the side it comes from is nought itself. */
    @Test
    void aDivisorPastEveryValueSendsItToNought() {
        NumericDomain.Bounds q =
                Intervals.roundedQuotient(between("1", "10"), between("2", null), 2);
        assertEquals("0", low(q));
        assertEquals("5.00", high(q));
    }

    /** A dividend running past every value leaves that end unbounded. */
    @Test
    void aDividendPastEveryValueLeavesThatEndUnbounded() {
        NumericDomain.Bounds q = Intervals.roundedQuotient(between("0", null), at("3"), 2);
        assertEquals("0", low(q));
        assertNull(high(q));
    }
}
