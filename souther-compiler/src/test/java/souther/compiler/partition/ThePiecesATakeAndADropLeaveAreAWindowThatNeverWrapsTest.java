package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.OptionalLong;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@code List.take} and {@code List.drop} leave of the pieces is a window, in the order they
 * were applied, and no count a program writes makes it mean another.
 */
class ThePiecesATakeAndADropLeaveAreAWindowThatNeverWrapsTest {

    private static PieceWindow window(long from, long until) {
        return new PieceWindow(from, OptionalLong.of(until));
    }

    @Test
    void takingAndDroppingDoNotCommute() {
        assertEquals(window(1, 3), PieceWindow.ALL.dropping(1).taking(2));
        assertEquals(window(1, 2), PieceWindow.ALL.taking(2).dropping(1));
    }

    @Test
    void aTakeOfAWindowEndsPastWhereItBeganAndNotPastWhereItEnds() {
        assertEquals(window(1, 2), PieceWindow.ALL.dropping(1).taking(5).taking(1));
        assertEquals(window(1, 4), PieceWindow.ALL.taking(4).dropping(1).taking(10));
    }

    @Test
    void aWindowThatStopsWhereItStartsIsTheOneWindowOfNone() {
        assertTrue(PieceWindow.ALL.taking(0).isEmpty());
        assertTrue(PieceWindow.ALL.taking(1).dropping(1).isEmpty());
        assertTrue(PieceWindow.ALL.taking(1).dropping(7).isEmpty());
        assertEquals(PieceWindow.ALL.taking(0), PieceWindow.ALL.taking(2).dropping(5));
        assertFalse(PieceWindow.ALL.isEmpty());
        assertFalse(PieceWindow.ALL.dropping(1_000).isEmpty());
    }

    /** Dropped three times as many as an int holds, the index is past every piece and stays. */
    @Test
    void noCountWrapsRoundIntoAWindowOfSome() {
        long big = 9_223_372_036_854_775_807L;
        PieceWindow past = PieceWindow.ALL.dropping(big).dropping(big).dropping(big);
        assertEquals(big, past.from());
        assertFalse(past.isEmpty());
        assertTrue(past.taking(5).isEmpty());
        assertEquals(OptionalLong.of(big), PieceWindow.ALL.taking(big).taking(big).until());
        assertEquals(OptionalLong.of(big), PieceWindow.ALL.dropping(1).taking(big).until());
    }

    @Test
    void aWindowThatStartsAtTheFirstIsTheOneThePiecesOfAStringAre() {
        assertTrue(PieceWindow.ALL.startsAtTheFirst());
        assertTrue(PieceWindow.ALL.taking(3).startsAtTheFirst());
        assertFalse(PieceWindow.ALL.dropping(1).startsAtTheFirst());
    }
}
