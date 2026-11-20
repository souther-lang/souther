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
        assertTrue(february().someDateHas(TakenAs.DatePart.DAY, 1));
        assertTrue(february().someDateHas(TakenAs.DatePart.DAY, 28));
        assertTrue(february().someDateHas(TakenAs.DatePart.DAY, 29));
    }

    @Test
    void aDayNoFebruaryHasIsNotShown() {
        assertFalse(february().someDateHas(TakenAs.DatePart.DAY, 30));
        assertFalse(february().someDateHas(TakenAs.DatePart.DAY, 31));
    }
}
