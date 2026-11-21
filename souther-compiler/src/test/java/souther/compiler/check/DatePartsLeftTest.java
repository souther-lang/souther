package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.TakenAs;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** Which parts of a date, once moved, a class of dates shows some date to have. */
class DatePartsLeftTest {

    private static final Endpoint TWO = Endpoint.inclusive(Count.of(2));
    private static final DatePartsLeft FEBRUARY =
            new DatePartsLeft(Map.of(TakenAs.DatePart.MONTH, new NumericDomain.Bounds(TWO, TWO)));

    /** The last day a February has is shown, and the one after is not. */
    @Test
    void aDayAFebruaryHasIsShownAndTheNextIsNot() {
        assertTrue(FEBRUARY.someDateHas(TakenAs.DatePart.DAY, 29, DateTranslation.none()));
        assertFalse(FEBRUARY.someDateHas(TakenAs.DatePart.DAY, 30, DateTranslation.none()));
    }

    /** A date a day on from a February is in February or is the first of March: never a thirtieth,
     *  and a month of March. */
    @Test
    void aPartOfADateMovedIsShownOfTheDatesTheMoveBrings() {
        DateTranslation aDayOn = DateTranslation.none().thenAddDays(1);
        assertFalse(FEBRUARY.someDateHas(TakenAs.DatePart.DAY, 30, aDayOn));
        assertTrue(FEBRUARY.someDateHas(TakenAs.DatePart.MONTH, 3, aDayOn));
    }

    /** Where nothing is said of the date, any part the calendar has is shown, however far moved:
     *  a year far from the calendar's first as well, which a search from the first would not
     *  reach. */
    @Test
    void whereNothingIsSaidOfTheDateEveryPartTheCalendarHasIsShown() {
        DateTranslation far = DateTranslation.none().thenAddDays(1_000);
        assertTrue(DatePartsLeft.EVERY_DATE.someDateHas(TakenAs.DatePart.DAY, 31, far));
        assertFalse(DatePartsLeft.EVERY_DATE.someDateHas(TakenAs.DatePart.DAY, 32, far));
        assertTrue(DatePartsLeft.EVERY_DATE.someDateHas(TakenAs.DatePart.YEAR, 2026, far));
    }

    /** A step on and the step back move nothing, and are defined at no date the first step is
     *  not: of the dates of the last year, the thirty-first of December has none, so it is not
     *  shown, and the thirtieth is. */
    @Test
    void aDateTheMoveIsNotDefinedAtIsNotShown() {
        DateTranslation there = DateTranslation.none().thenAddDays(1).thenAddDays(-1);
        Endpoint lastYear = Endpoint.inclusive(Count.of(999_999_999));
        Endpoint december = Endpoint.inclusive(Count.of(12));
        DatePartsLeft lastDay = new DatePartsLeft(Map.of(
                TakenAs.DatePart.YEAR, new NumericDomain.Bounds(lastYear, lastYear),
                TakenAs.DatePart.MONTH, new NumericDomain.Bounds(december, december)));
        assertTrue(lastDay.someDateHas(TakenAs.DatePart.DAY, 30, there));
        assertFalse(lastDay.someDateHas(TakenAs.DatePart.DAY, 31, there));
    }
}
