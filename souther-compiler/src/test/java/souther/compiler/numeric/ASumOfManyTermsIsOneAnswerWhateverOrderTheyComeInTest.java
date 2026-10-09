package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The exact sum of many terms is one answer for the terms, in whatever order they come.
 *
 * <p>A run of two-term sums left to right is not: a fine term and an ordinary one far apart in
 * scale cannot be held together, so a fine term, a whole one and the fine term's negation fail
 * where the first two meet and come to the whole one where the two fine terms meet first. A sum of
 * many meets terms of one scale first, so the answer is the terms' and not their order's.
 */
class ASumOfManyTermsIsOneAnswerWhateverOrderTheyComeInTest {

    /** A tenth to the power of a scale near the end of the range: added to one, no number the
     *  exact arithmetic holds. */
    private static final ExactRatio FINE = ExactRatio.of(new BigDecimal(BigInteger.ONE, 1 << 30));

    @Test
    void aFineTermAndItsNegationCancelWhereverTheWholeOneStands() {
        for (List<ExactRatio> order : orders(List.of(FINE, ExactRatio.ONE, FINE.negated()))) {
            assertEquals(ExactAnswer.held(ExactRatio.ONE), ExactRatio.sum(order),
                    () -> "summed in the order " + order);
        }
    }

    @Test
    void finePartsOfSeveralScalesCancelBeforeTheWholeOneIsMet() {
        ExactRatio twice = FINE.plus(FINE).orFail("twice a fine term is held");
        ExactRatio thrice = twice.plus(FINE).orFail("three times a fine term is held");
        for (List<ExactRatio> order : orders(List.of(FINE, twice, thrice.negated(),
                ExactRatio.ONE))) {
            assertEquals(ExactAnswer.held(ExactRatio.ONE), ExactRatio.sum(order),
                    () -> "summed in the order " + order);
        }
    }

    @Test
    void aSumNoNumberHoldsIsRefusedWhateverTheOrder() {
        for (List<ExactRatio> order : orders(List.of(FINE, ExactRatio.ONE))) {
            assertInstanceOf(ExactAnswer.Unheld.class, ExactRatio.sum(order),
                    () -> "summed in the order " + order);
        }
    }

    @Test
    void nothingSumsToNought() {
        assertEquals(ExactAnswer.held(ExactRatio.ZERO), ExactRatio.sum(List.of()));
    }

    @Test
    void theWeightsOfOneAtomInSeveralFormsAreOneSumWhateverOrderTheFormsComeIn() {
        List<LinearForm<String>> forms = List.of(LinearForm.weighing("x", FINE),
                LinearForm.weighing("x", ExactRatio.ONE),
                LinearForm.weighing("x", FINE.negated()));
        for (List<LinearForm<String>> order : orders(forms)) {
            assertEquals(ExactAnswer.held(LinearForm.atom("x")), LinearForm.sum(order),
                    () -> "summed in the order " + order);
        }
        Map<String, ExactRatio> none = new LinkedHashMap<>();
        assertEquals(ExactAnswer.held(new LinearForm<>(ExactRatio.ZERO, none)),
                LinearForm.sum(List.of(LinearForm.weighing("x", FINE),
                        LinearForm.weighing("x", FINE.negated()))),
                "and an atom whose weights cancel is no atom of the sum");
    }

    /** Every order of {@code terms}. */
    private static <T> List<List<T>> orders(List<T> terms) {
        if (terms.isEmpty()) {
            return List.of(List.of());
        }
        List<List<T>> out = new ArrayList<>();
        for (int i = 0; i < terms.size(); i++) {
            List<T> rest = new ArrayList<>(terms);
            T first = rest.remove(i);
            for (List<T> tail : orders(rest)) {
                List<T> one = new ArrayList<>();
                one.add(first);
                one.addAll(tail);
                out.add(one);
            }
        }
        return out;
    }
}
