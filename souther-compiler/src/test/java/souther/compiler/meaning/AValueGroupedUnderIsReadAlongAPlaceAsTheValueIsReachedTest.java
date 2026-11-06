package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What reads a place reads the value elements are grouped under ({@link
 * Quantity.TheValue#isReadAlong}) where the place is where the value is held, inside it or holds it
 * as the value is reached: a name read at an element is the name read at each case of it, and a
 * place under another case of the element reads none of the value.
 */
class AValueGroupedUnderIsReadAlongAPlaceAsTheValueIsReachedTest {

    private static final TermPath ELEMENT = TermPath.of("r").then("items").element();
    private static final TermPath STOCKED = ELEMENT.refine(
            Refinement.of(new Case.Presence(true)));
    private static final TermPath OUT = ELEMENT.refine(Refinement.of(new Case.Presence(false)));

    private static Quantity.TheValue at(TermPath place) {
        return new Quantity.TheValue.AtAPlace(new DecisionSubject.AnInput(place));
    }

    @Test
    void theNameReadAtTheElementIsTheNameReadAtACaseOfTheElement() {
        assertTrue(at(STOCKED.then("sku")).isReadAlong(ELEMENT.then("sku")));
        assertTrue(at(ELEMENT.then("sku")).isReadAlong(STOCKED.then("sku")));
        assertTrue(at(STOCKED.then("sku")).isReadAlong(ELEMENT));
    }

    @Test
    void anotherFieldOfTheElementIsNot() {
        assertFalse(at(STOCKED.then("sku")).isReadAlong(ELEMENT.then("qty")));
        assertFalse(at(ELEMENT.then("sku")).isReadAlong(STOCKED.then("qty")));
    }

    /** The value held under one case is read by nothing under the other, though a statement under
     *  the other excludes it ({@link TermPath#bearsOn}). */
    @Test
    void aPlaceUnderAnotherCaseOfTheElementIsNot() {
        assertFalse(at(STOCKED.then("sku")).isReadAlong(OUT.then("sku")));
        assertFalse(at(STOCKED.then("sku")).isReadAlong(OUT));
        assertTrue(STOCKED.then("sku").bearsOn(OUT.then("sku")));
    }
}
