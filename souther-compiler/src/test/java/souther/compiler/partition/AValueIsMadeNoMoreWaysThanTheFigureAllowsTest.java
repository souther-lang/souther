package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The ways a row makes a value a number are made to the one figure there is for them: no more are
 * made than it allows, whatever the rule that makes them is made of, and what was not made is said
 * to have been left. The ways made are all that is looked at, so a reader is never handed what was
 * built past the figure.
 */
class AValueIsMadeNoMoreWaysThanTheFigureAllowsTest {

    private static Attainment way(long to) {
        return Attainment.always(LinearForm.constant(ExactRatio.of(to)));
    }

    @Test
    void theMostWaysThereIsRoomForAreMadeAndNothingIsLeft() {
        Attainments.Builder made = new Attainments.Builder();
        for (int at = 0; at < Attainments.MOST; at++) {
            assertTrue(made.add(way(at)));
        }
        assertFalse(made.hasRoom());
        assertEquals(Attainments.MOST, made.build().ways().size());
        assertFalse(made.build().leftUnmade(), "the last of the room was used, and nothing was "
                + "left for want of it");
    }

    @Test
    void aWayBeyondTheFigureIsNotMadeAndIsSaidLeft() {
        Attainments.Builder made = new Attainments.Builder();
        for (int at = 0; at < Attainments.MOST; at++) {
            made.add(way(at));
        }
        assertFalse(made.add(way(Attainments.MOST)));
        Attainments built = made.build();
        assertEquals(Attainments.MOST, built.ways().size(), "no more than the figure is made");
        assertTrue(built.leftUnmade());
    }

    @Test
    void whatWasLeftUnmadeOfWhatThisIsMadeOfIsLeftUnmadeOfThisAsWell() {
        Attainments.Builder made = new Attainments.Builder();
        made.noting(Attainments.TOO_MANY);
        made.add(way(1));
        assertTrue(made.hasRoom(), "what was left unmade took no room of what is made");
        assertTrue(made.build().leftUnmade());
        assertEquals(1, made.build().ways().size());
    }
}
