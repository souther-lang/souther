package souther.compiler.collect;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What one of these reads is what it was told and what the one it was told on read, whichever other
 * values were told something on the same line or on a line of their own; and a line told one at a
 * time is one table, so a path naming one more thing at each step copies nothing.
 */
class AValueToldOneMoreReadsWhatItWasToldAndNoMoreTest {

    /**
     * A line told a thousand entries one at a time copies none of them, and a value told something
     * from halfway along it copies the half it reads — which is also what says the count is being
     * kept, since a count nobody kept says no copying happened either.
     */
    @Test
    void aLineToldOneAtATimeCopiesNothingAndALineFromHalfwayCopiesWhatItReads() {
        long[] counting = {0};
        AppendOnly.COUNTING_COPIED = counting;
        try {
            AppendOnly<Integer, String> told = AppendOnly.empty();
            AppendOnly<Integer, String> halfway = null;
            for (int i = 0; i < 1000; i++) {
                told = told.with(i, "v" + i);
                if (i == 499) {
                    halfway = told;
                }
            }
            assertEquals("v999", told.get(999));
            assertEquals(0, counting[0]);

            AppendOnly<Integer, String> beside = halfway.with(-1, "beside");
            assertEquals(500, counting[0]);
            assertEquals("beside", beside.get(-1));
            assertFalse(told.contains(-1));
        } finally {
            AppendOnly.COUNTING_COPIED = null;
        }
    }

    @Test
    void whetherAKeyWasToldIsAskedOfTheEntryAndNothingToldIsNull() {
        AppendOnly<String, Integer> told = AppendOnly.<String, Integer>empty().with("a", 1);
        assertTrue(told.contains("a"));
        assertFalse(told.contains("b"));
        assertThrows(NullPointerException.class, () -> told.with("b", null));
        assertFalse(told.contains("b"));
    }

    @Test
    void aValueDoesNotReadWhatWasToldAfterIt() {
        AppendOnly<String, Integer> earlier = AppendOnly.<String, Integer>empty().with("a", 1);
        AppendOnly<String, Integer> later = earlier.with("b", 2);
        assertNull(earlier.get("b"));
        assertEquals(Set.of("a"), earlier.keys());
        assertEquals(2, later.get("b"));
    }

    @Test
    void twoLinesFromOnePlaceDoNotReadEachOther() {
        AppendOnly<String, Integer> from = AppendOnly.<String, Integer>empty().with("a", 1);
        AppendOnly<String, Integer> one = from.with("b", 2);
        AppendOnly<String, Integer> other = from.with("b", 3).with("c", 4);
        AppendOnly<String, Integer> further = one.with("d", 5);

        assertEquals(Map.of("a", 1, "b", 2), one.asMap());
        assertEquals(Map.of("a", 1, "b", 3, "c", 4), other.asMap());
        assertEquals(Map.of("a", 1, "b", 2, "d", 5), further.asMap());
        assertEquals(Map.of("a", 1), from.asMap());
    }

    @Test
    void whatIsReadIsInTheOrderItWasTold() {
        AppendOnly<String, Integer> told =
                AppendOnly.<String, Integer>empty().with("z", 1).with("a", 2).with("m", 3);
        assertEquals(List.of("z", "a", "m"), List.copyOf(told.keys()));
        assertEquals(List.of("z", "a", "m"), List.copyOf(told.asMap().keySet()));
    }

    @Test
    void aKeyIsToldOnce() {
        AppendOnly<String, Integer> told = AppendOnly.<String, Integer>empty().with("a", 1);
        assertThrows(IllegalArgumentException.class, () -> told.with("a", 2));
    }
}
