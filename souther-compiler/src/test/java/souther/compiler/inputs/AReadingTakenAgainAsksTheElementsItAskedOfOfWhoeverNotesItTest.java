package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading that is part of another and is taken from a reading made before is asked of the same
 * elements by whoever notes the other: what the footprint of the whole says is the same whether the
 * part was read or taken, or the whole would be taken at a reading its elements stand otherwise at.
 */
class AReadingTakenAgainAsksTheElementsItAskedOfOfWhoeverNotesItTest {

    private static final ElementsNamed.Slot AN_ITEM = ElementsNamed.Slot.innermostOf(
            TermPath.of("x").then("items").element());

    private static final BindingOwner OWNER = new BindingOwner.OfValue("probe", "f");
    private static final BindingId A = new BindingId(OWNER, 1);
    private static final BindingId B = new BindingId(OWNER, 2);

    private static ElementsNamed through(BindingId name) {
        return ElementsNamed.of(List.of(new ElementsNamed.Named(AN_ITEM, name)));
    }

    /** The footprint of reading an element through {@code name}, once. */
    private static ElementsMet.Footprint readThrough(BindingId name) {
        ElementsMet met = new ElementsMet();
        ElementsMet.Noting noting = met.noting();
        met.admits(through(name));
        return noting.ended();
    }

    /** The footprint of a whole that is made of a part taken from a reading made before. */
    private static ElementsMet.Footprint wholeTaking(ElementsMet.Footprint part) {
        ElementsMet met = new ElementsMet();
        ElementsMet.Noting noting = met.noting();
        met.takes(part);
        return noting.ended();
    }

    @Test
    void aWholeThatTookItsPartIsAskedAfterTheElementsThePartAskedOf() {
        ElementsMet.Footprint read = readThrough(A);
        ElementsMet.Footprint taken = wholeTaking(readThrough(A));
        assertNotNull(taken);
        ElementsMet standingForB = new ElementsMet();
        standingForB.admits(through(B));
        ElementsMet standingForA = new ElementsMet();
        standingForA.admits(through(A));
        ElementsMet nothingMet = new ElementsMet();
        for (ElementsMet where : List.of(standingForA, standingForB, nothingMet)) {
            assertEquals(where.agrees(read), where.agrees(taken),
                    "a whole that took its part is asked what a whole that read it is");
        }
        assertTrue(nothingMet.agrees(taken), "it began with no element met");
        assertFalse(standingForA.agrees(taken), "and is not taken where one stands for the element");
        assertFalse(standingForB.agrees(taken));
    }
}
