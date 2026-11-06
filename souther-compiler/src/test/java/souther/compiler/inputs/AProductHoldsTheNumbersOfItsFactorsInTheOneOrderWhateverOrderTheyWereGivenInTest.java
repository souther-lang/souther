package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two products that are equal are read alike by whoever reads them.
 *
 * <p>A form is a mapping, so a factor written {@code a + b} and one written {@code b + a} are equal
 * and hold their numbers in different orders. What a product is equal to says nothing of that
 * order, and everything that reads one — the text it is written as, where a reader is sent, the
 * order its numbers are placed in — would otherwise answer by it. The product is where the order is
 * settled, once, so that a reader added later has nothing to remember.
 */
class AProductHoldsTheNumbersOfItsFactorsInTheOneOrderWhateverOrderTheyWereGivenInTest {

    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("a"));

    private static final NumericTerm B = new NumericTerm.ValueOf(TermPath.of("b"));

    private static final NumericTerm C = new NumericTerm.ValueOf(TermPath.of("c"));

    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("d"));

    @Test
    void twoEqualProductsAreWrittenAndSentToTheSamePlace() {
        NumericTerm.ProductOf forward = product(List.of(A, B), List.of(C, D));
        NumericTerm.ProductOf backward = product(List.of(B, A), List.of(D, C));

        assertEquals(forward, backward);
        assertEquals(forward.spelling(), backward.spelling(),
                "equal products are written two ways");
        assertEquals(forward.subjectPath(), backward.subjectPath(),
                "equal products send a reader to two places");
    }

    @Test
    void eachFactorHoldsItsNumbersAsTheyAreOrderedAndNotAsTheyWereGiven() {
        for (NumericTerm.ProductOf product : List.of(
                product(List.of(A, B), List.of(C, D)), product(List.of(B, A), List.of(D, C)))) {
            for (LinearForm<NumericTerm> factor : product.factors()) {
                assertEquals(NumericTerms.inOrder(factor.coefs().keySet()),
                        List.copyOf(factor.coefs().keySet()));
            }
        }
    }

    private static NumericTerm.ProductOf product(List<NumericTerm> first, List<NumericTerm> second) {
        return NumericTerm.ProductOf.of(form(first), form(second));
    }

    private static LinearForm<NumericTerm> form(List<NumericTerm> inThatOrder) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (NumericTerm each : inThatOrder) {
            coefs.put(each, ExactRatio.ONE);
        }
        return new LinearForm<>(ExactRatio.ZERO, coefs);
    }
}
