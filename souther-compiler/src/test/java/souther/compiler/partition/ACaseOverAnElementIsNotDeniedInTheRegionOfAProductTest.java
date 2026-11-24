package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A case another reading decides in is denied in a region only where it is about the input as a
 * whole. A case over an element is asked of a row under each choice of the element, and a region
 * holds one position for every element, so denying it there would leave out a row whose chosen
 * element is in the class while another is in the case.
 *
 * <p>Which a term is over is every place it is read off. A product reads two, and the place it is
 * sent to a reader at is only the first number's.
 */
class ACaseOverAnElementIsNotDeniedInTheRegionOfAProductTest {

    private static final NumericTerm N = new NumericTerm.ValueOf(TermPath.of("a"));

    private static final NumericTerm AN_ELEMENT =
            new NumericTerm.ValueOf(TermPath.of("z").element().then("value"));

    @Test
    void aProductWithAnElementInItsSecondFactorIsInsideAContainer() {
        NumericTerm.ProductOf nFirst =
                NumericTerm.ProductOf.of(LinearForm.atom(N), LinearForm.atom(AN_ELEMENT));
        NumericTerm.ProductOf elementFirst =
                NumericTerm.ProductOf.of(LinearForm.atom(AN_ELEMENT), LinearForm.atom(N));

        assertNotNull(nFirst, "two numbers read off two places are a product");
        assertNotNull(elementFirst, "and so are they the other way round");
        assertTrue(OutsideTheOtherReadings.insideAContainer(nFirst));
        assertTrue(OutsideTheOtherReadings.insideAContainer(elementFirst));
        assertTrue(!nFirst.subjectPath().insideAContainer()
                        || !elementFirst.subjectPath().insideAContainer(),
                "one of the two is sent to a reader at the first number's place, outside the"
                        + " container");
    }

    @Test
    void aNumberOfTheInputAloneIsNot() {
        assertFalse(OutsideTheOtherReadings.insideAContainer(N));
    }

    @Test
    void aNumberOfAnElementIs() {
        assertTrue(OutsideTheOtherReadings.insideAContainer(AN_ELEMENT));
    }
}
