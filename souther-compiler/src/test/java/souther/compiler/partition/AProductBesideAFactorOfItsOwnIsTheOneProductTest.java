package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

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
                        of(product, weighed, factor, besideWeighed), null);
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
        LinearForm<Quantity> together = FactoredProducts.of(form, null);
        assertEquals(2, together.coefs().size(), together::toString);
        assertEquals(true, together.coefs().containsKey(new DecisionAtom.OfTheInput(C)),
                together::toString);
    }

    @Test
    void aFormWithNoProductInItIsTheSameForm() {
        LinearForm<Quantity> form = of(new DecisionAtom.OfTheInput(A), 1,
                new DecisionAtom.OfTheInput(B), -1);
        assertEquals(form, FactoredProducts.of(form, null));
    }
}
