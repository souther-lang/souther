package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ElementBindings;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A step a walk takes again from a reading makes the reading it made the first time, so that two
 * walks of one body meet on one value and a key made of it is compared by identity. A step made
 * with another node makes another reading, equal or not.
 */
class AStepTakenAgainMakesTheReadingItMadeBeforeTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "go");
    private static final Core.Binder X = new Core.Binder("x", new BindingId(OWNER, 1));

    private static final InputReads TOP = InputReads.ofParameters(
            Map.of(new BindingId(OWNER, 0), "p"), DeclaredInput.NONE, ElementBindings.NONE,
            ValueDefinitions.NONE, souther.compiler.carrier.Membership.none());

    @Test
    void aBindingEnteredAgainIsTheReadingEnteredBefore() {
        Core one = new Core.Int(1, Type.INT, POS);

        assertSame(TOP.and(X, one), TOP.and(X, one));
    }

    @Test
    void aBindingOfAnotherNodeIsAnotherReading() {
        Core one = new Core.Int(1, Type.INT, POS);
        Core another = new Core.Int(1, Type.INT, POS);

        assertNotSame(TOP.and(X, one), TOP.and(X, another));
        assertEquals(TOP.and(X, one), TOP.and(X, another));
    }

    /** A walk that follows the names alone, as a walk after where a value stands does, meets the
     *  reading inside the binding on its names. */
    @Test
    void theNamesEnteredAloneAreTheNamesOfTheReadingEntered() {
        Core one = new Core.Int(1, Type.INT, POS);

        assertSame(TOP.and(X, one).names(), TOP.names().inside(X, one));
    }
}
