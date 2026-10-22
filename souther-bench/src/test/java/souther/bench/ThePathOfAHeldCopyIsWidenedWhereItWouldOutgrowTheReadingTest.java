package souther.bench;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A path of a held copy is as long as the reading follows and no longer, and widening it says more
 * and never less.
 *
 * <p>The paths are slots over {@code e} and {@code k}, and the reading settles because there are
 * finitely many of them. Widened, a path keeps its first slots and ends in {@code *}, which says
 * that the copy is that deep or deeper.
 */
class ThePathOfAHeldCopyIsWidenedWhereItWouldOutgrowTheReadingTest {

    @Test
    void aPathOfAsManySlotsAsTheReadingFollowsIsNotChanged() {
        String longest = "ekek".substring(0, HeldCopies.MAX_DEPTH);

        assertEquals(longest, HeldCopies.widened(longest));
        assertEquals("e", HeldCopies.widened("e"));
        assertEquals("*", HeldCopies.widened("*"));
    }

    @Test
    void aLongerPathKeepsItsFirstSlotsAndSaysItGoesOn() {
        String slots = "ekekekek";

        assertEquals(slots.substring(0, HeldCopies.MAX_DEPTH) + "*", HeldCopies.widened(slots));
    }

    @Test
    void aPathThatGoesOnAlreadyIsWidenedTheSameWay() {
        String longer = "e".repeat(HeldCopies.MAX_DEPTH + 3) + "*";

        assertEquals("e".repeat(HeldCopies.MAX_DEPTH) + "*", HeldCopies.widened(longer));
        assertEquals("e*", HeldCopies.widened("e*"));
    }

    @Test
    void widenedTwiceIsWidenedOnce() {
        for (String each : new String[] {"e", "ek", "ekeek", "eeeee*", "*", "kkkkkkkkk"}) {
            assertEquals(HeldCopies.widened(each), HeldCopies.widened(HeldCopies.widened(each)),
                    () -> "widening " + each + " is not a settled thing");
        }
    }
}
