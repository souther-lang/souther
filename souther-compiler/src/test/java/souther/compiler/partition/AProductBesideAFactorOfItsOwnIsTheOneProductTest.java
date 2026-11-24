package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A product beside a factor of its own is the one product of that number and the form beside it:
 * {@code a * b - a} is {@code a * (b - 1)}, a relation about a number at one value and a form at
 * another, where over {@code a} and {@code a * b} it would be about two values of one place.
 */
class AProductBesideAFactorOfItsOwnIsTheOneProductTest {

    private static final NumericTerm.ValueOf A = new NumericTerm.ValueOf(TermPath.of("a"));
    private static final NumericTerm.ValueOf B = new NumericTerm.ValueOf(TermPath.of("b"));
    private static final NumericTerm.ValueOf C = new NumericTerm.ValueOf(TermPath.of("c"));

    private static LinearForm<Quantity> of(Quantity product, long weighed, Quantity beside,
                                           long besideWeighed) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(product, ExactRatio.of(weighed));
        coefs.put(beside, ExactRatio.of(besideWeighed));
        return new LinearForm<>(ExactRatio.ZERO, coefs);
    }

    @Test
    void aProductAndItsFactorAreOneProductOfTheNumberAndWhatIsBesideIt() {
        Quantity product = new Quantity.ProductOfTwo(A, B);
        Quantity factor = new DecisionAtom.OfTheInput(A);
        for (long weighed : new long[] {1, -1, 3}) {
            for (long besideWeighed : new long[] {1, -1, -2}) {
                LinearForm<Quantity> together = FactoredProducts.of(
                        of(product, weighed, factor, besideWeighed));
                assertEquals(1, together.coefs().size(), weighed + " and " + besideWeighed
                        + " come to " + together);
                assertEquals(DecisionAtom.OfTheInput.class,
                        together.coefs().keySet().iterator().next().getClass(), together::toString);
            }
        }
    }

    @Test
    void aProductBesideANumberItHasNoFactorOfIsLeftAsItIsWrittenBeside() {
        LinearForm<Quantity> form = of(new Quantity.ProductOfTwo(A, B), 1,
                new DecisionAtom.OfTheInput(C), -1);
        LinearForm<Quantity> together = FactoredProducts.of(form);
        assertEquals(2, together.coefs().size(), together::toString);
        assertEquals(true, together.coefs().containsKey(new DecisionAtom.OfTheInput(C)),
                together::toString);
    }

    /**
     * Two writings of one product are one atom with the weights added; where the exact arithmetic
     * cannot add them the form is left as it was. A sum that went unheld is not a sum of nothing,
     * and an atom taken out of a form is a relation with a term gone.
     */
    @Test
    void weightsThatCannotBeAddedLeaveTheFormAsItWas() {
        ExactRatio wide = ExactRatio.tenTo(Long.MAX_VALUE / 4);
        assertTrue(wide.plus(ExactRatio.of(-1)) instanceof ExactAnswer.Unheld<ExactRatio>,
                "the weights below are ones the arithmetic cannot add");
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(new Quantity.ProductOfTwo(A, B), wide);
        coefs.put(new DecisionAtom.OfTheInput(NumericTerm.ProductOf.of(
                LinearForm.atom(A), LinearForm.atom(B))), ExactRatio.of(-1));
        LinearForm<Quantity> form = new LinearForm<>(ExactRatio.ZERO, coefs);
        assertEquals(form, FactoredProducts.of(form));
    }

    @Test
    void aFormWithNoProductInItIsTheSameForm() {
        LinearForm<Quantity> form = of(new DecisionAtom.OfTheInput(A), 1,
                new DecisionAtom.OfTheInput(B), -1);
        assertEquals(form, FactoredProducts.of(form));
    }
}
