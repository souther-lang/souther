package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A reading being noted that ends by an exception stops being noted, and the reading around it is
 * told the elements it asked of ({@link ElementsMet.Noting#close}).
 *
 * <p>The reading around may go on past the one that stopped and come to something, and what it
 * comes to then turns on what the stopped one asked of: a footprint without those elements would
 * let it be taken where they stand otherwise.
 */
class AReadingThatStopsTellsTheReadingAroundWhatItAskedOfTest {

    private static final ElementsNamed.Slot AN_ITEM = ElementsNamed.Slot.innermostOf(
            TermPath.of("x").then("items").element());

    private static final BindingOwner OWNER = new BindingOwner.OfValue("probe", "f");
    private static final BindingId A = new BindingId(OWNER, 1);
    private static final BindingId B = new BindingId(OWNER, 2);

    private static ElementsNamed through(BindingId name) {
        return ElementsNamed.of(List.of(new ElementsNamed.Named(AN_ITEM, name)));
    }

    @Test
    void theReadingAroundOneThatStoppedAskedOfWhatItAskedOf() {
        ElementsMet met = new ElementsMet();
        ElementsMet.Noting around = met.noting();

        assertThrows(IllegalStateException.class, () -> {
            try (ElementsMet.Noting _ = met.noting()) {
                met.admits(through(A), Set.of());
                throw new IllegalStateException("the reading stopped");
            }
        });
        ElementsMet.Footprint whole = around.ended();

        ElementsMet standingForB = new ElementsMet();
        standingForB.admits(through(B), Set.of());
        assertFalse(standingForB.agrees(whole),
                "the element the stopped reading asked of is in the footprint of the one around");
    }
}
