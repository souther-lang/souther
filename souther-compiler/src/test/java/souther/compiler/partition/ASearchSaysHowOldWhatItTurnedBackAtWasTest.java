package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a search for a way in has gone into is numbered in the order it was met, and what it turns
 * back at says how old that was: a part that turned back at something met before it began is not
 * answered on its own, and is not kept ({@code Pullback#goneIntoAlone}).
 */
class ASearchSaysHowOldWhatItTurnedBackAtWasTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final BindingOwner OWNER = new BindingOwner.OfValue("m", "v");

    private static Core node(int index) {
        return new Core.Read("n" + index, new BindingId(OWNER, index), Type.INT, POS);
    }

    @Test
    void aValueGoneIntoIsGoneIntoOnceAtOneReading() {
        Pullback.Gone gone = new Pullback.Gone();
        Core first = node(0);

        assertTrue(gone.firstGoingInto(first, null));
        assertFalse(gone.firstGoingInto(first, null));
        assertEquals(1, gone.met);
    }

    @Test
    void whatASearchTurnsBackAtIsAsOldAsWhenItWasMet() {
        Pullback.Gone gone = new Pullback.Gone();
        Core early = node(0);
        Core late = node(1);
        gone.firstGoingInto(early, null);
        gone.firstGoingInto(late, null);

        gone.firstGoingInto(late, null);
        assertEquals(1, gone.oldestTurnedBackAt);

        gone.firstGoingInto(early, null);
        assertEquals(0, gone.oldestTurnedBackAt, "the oldest of what it turned back at");
    }

    @Test
    void aBindingReadThroughAgainIsTurnedBackAtAsAValueIs() {
        Pullback.Gone gone = new Pullback.Gone();
        BindingId binding = new BindingId(OWNER, 7);

        assertTrue(gone.firstReadingThrough(binding));
        assertFalse(gone.firstReadingThrough(binding));
        assertEquals(0, gone.oldestTurnedBackAt);
    }
}
