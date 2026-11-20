package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.TakenAs;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** Which parts of a date a class of dates shows some date to have. */
class DatePartsLeftTest {

    private static DatePartsLeft february() {
        Endpoint two = Endpoint.inclusive(Count.of(2));
        return new DatePartsLeft(Map.of(TakenAs.DatePart.MONTH, new NumericDomain.Bounds(two, two)));
    }

    @Test
    void aDayAFebruaryHasIsShown() {
        for (int day : new int[] {1, 28, 29}) {
            assertTrue(DatePartsLeft.someDateHas(february(), TakenAs.DatePart.DAY, day, 0), "" + day);
        }
    }

    @Test
    void aDayNoFebruaryHasIsNotShown() {
        for (int day : new int[] {30, 31}) {
            assertFalse(DatePartsLeft.someDateHas(february(), TakenAs.DatePart.DAY, day, 0), "" + day);
        }
    }

    /** A date a day on from a February is the first of March or in February, so it is never the
     *  thirty-first, and is the first of a March. */
    @Test
    void aDayAFebruaryComesToOnceMovedIsShownOnlyWhereOneDoes() {
        assertFalse(DatePartsLeft.someDateHas(february(), TakenAs.DatePart.DAY, 31, 1));
        assertFalse(DatePartsLeft.someDateHas(february(), TakenAs.DatePart.DAY, 30, 1));
        assertTrue(DatePartsLeft.someDateHas(february(), TakenAs.DatePart.DAY, 29, 1));
        assertTrue(DatePartsLeft.someDateHas(february(), TakenAs.DatePart.MONTH, 3, 1));
        assertFalse(DatePartsLeft.someDateHas(february(), TakenAs.DatePart.MONTH, 4, 1));
    }

    @Test
    void whereTheDatesAreLeftNoPartTheCalendarHasIsLeftOut() {
        assertTrue(DatePartsLeft.someDateHas(null, TakenAs.DatePart.DAY, 31, 0));
        assertTrue(DatePartsLeft.someDateHas(null, TakenAs.DatePart.DAY, 31, 1_000));
        assertTrue(DatePartsLeft.someDateHas(null, TakenAs.DatePart.DAY, 31, -1_000));
        assertFalse(DatePartsLeft.someDateHas(null, TakenAs.DatePart.DAY, 32, 0));
    }
}
