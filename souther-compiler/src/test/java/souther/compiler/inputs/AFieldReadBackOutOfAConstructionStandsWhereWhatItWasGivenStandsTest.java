package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A field read back out of a construction is the value the construction was given for it, and
 * stands in the element where that value does — the cancellation a position of the input is read
 * by, in the way inside one value.
 *
 * <p>Held here rather than through a model, because which shape a body leaves a read of a field
 * in — an access, a projection of several names, a name standing for a projection — is the
 * compiler's to choose, and a model reaches only the shapes it happens to leave today.
 */
class AFieldReadBackOutOfAConstructionStandsWhereWhatItWasGivenStandsTest {

    private static final SourcePos POS = new SourcePos(0, 0);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("example", "f");
    private static final BindingId ELEMENT = new BindingId(OWNER, 0);
    private static final BindingId MADE = new BindingId(OWNER, 1);
    private static final BindingId INNER = new BindingId(OWNER, 2);
    private static final TypeSymbol.AtModule KEY =
            TypeSymbols.declared(new TypeKey("example", "Key"));
    private static final TypeSymbol.AtModule OUTER =
            TypeSymbols.declared(new TypeKey("example", "Outer"));

    /** The element's label, the value every construction here is given. */
    private static final Core LABEL = new Core.FieldAccess(
            new Core.Read("i", ELEMENT, Type.STRING, POS), "label", Type.STRING, POS);

    private static Core.Construct key() {
        return new Core.Construct(KEY, List.of(new Core.FieldValue("label", LABEL, POS)),
                Type.ref(KEY), POS);
    }

    private static Core.Construct outer() {
        return new Core.Construct(OUTER, List.of(new Core.FieldValue("key", key(), POS)),
                Type.ref(OUTER), POS);
    }

    private static ElementProjection read(Core answer, Map<BindingId, Core> held) {
        return ElementProjection.read(answer, ELEMENT, held, DeclarationNewtypes.NONE);
    }

    private static final ElementProjection THE_LABEL = new ElementProjection(List.of("label"));

    @Test
    void aFieldOfAConstructionIsWhereItWasGiven() {
        assertEquals(THE_LABEL, read(new Core.FieldAccess(key(), "label", Type.STRING, POS),
                Map.of()));
    }

    @Test
    void aFieldOfANameForAConstructionIsWhereItWasGiven() {
        assertEquals(THE_LABEL, read(new Core.FieldAccess(
                new Core.Read("made", MADE, Type.ref(KEY), POS), "label", Type.STRING, POS),
                Map.of(MADE, key())));
    }

    /** Names read off a construction one after another, as one projection, cancel one at a time. */
    @Test
    void theNamesOfAProjectionCancelAgainstTheConstructionsTheyRead() {
        Core projected = Core.FieldProjection.then(Core.FieldProjection.then(outer(), "key",
                Type.ref(KEY)), "label", Type.STRING);
        assertEquals(THE_LABEL, read(projected, Map.of()));
    }

    /** A name standing for a projection of a construction is what that projection was given. */
    @Test
    void aFieldOfANameForAProjectionOfAConstructionIsWhereItWasGiven() {
        Core inner = Core.FieldProjection.then(new Core.Read("made", MADE, Type.ref(OUTER), POS),
                "key", Type.ref(KEY));
        assertEquals(THE_LABEL, read(new Core.FieldAccess(
                new Core.Read("inner", INNER, Type.ref(KEY), POS), "label", Type.STRING, POS),
                Map.of(MADE, outer(), INNER, inner)));
    }

    /** A field of a value that is no construction is still no place of the element it was not
     *  read from. */
    @Test
    void aFieldOfSomethingElseIsNoPlaceOfTheElement() {
        assertNull(read(new Core.FieldAccess(new Core.Str("x", Type.STRING, POS), "label",
                Type.STRING, POS), Map.of()));
    }
}
