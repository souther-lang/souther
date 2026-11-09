package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The canonical form of a sum is the same whichever way the writing of it reaches it: a form
 * already in lowest terms is taken as it stands, and one that is not is scaled and has its
 * positions with no weight dropped, so two writings of one sum are one form.
 */
class AFormInLowestTermsIsItsOwnCanonicalFormTest {

    private static Map<String, ExactRatio> weighing(Object... pairs) {
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            out.put((String) pairs[i], ExactRatio.of((Integer) pairs[i + 1]));
        }
        return out;
    }

    private static CanonicalForm.Scaled<String> scaled(Map<String, ExactRatio> coefs) {
        if (CanonicalForm.of(coefs) instanceof CanonicalForm.Scaled<String> form) {
            return form;
        }
        throw new AssertionError(coefs + " is a sum of no weight");
    }

    @Test
    void aFormInLowestTermsIsTakenAsItStandsAndScaledByOne() {
        CanonicalForm.Scaled<String> form = scaled(weighing("a", 1, "b", -1));

        assertEquals(weighing("a", 1, "b", -1), form.form().coefs());
        assertEquals(ExactRatio.ONE, form.by());
    }

    @Test
    void aFormWhoseWeightsShareAFactorIsDividedByIt() {
        CanonicalForm.Scaled<String> form = scaled(weighing("a", 2, "b", -4));

        assertEquals(weighing("a", 1, "b", -2), form.form().coefs());
        assertEquals(ExactRatio.of(2), form.by());
    }

    @Test
    void aPositionWithNoWeightIsDroppedWhetherOrNotTheOthersShareAFactor() {
        assertEquals(weighing("a", 1, "b", -1), scaled(weighing("a", 1, "z", 0, "b", -1)).form().coefs());
        assertEquals(weighing("a", 1, "b", -2), scaled(weighing("a", 2, "z", 0, "b", -4)).form().coefs());
    }

    @Test
    void twoWritingsOfOneSumAreOneForm() {
        assertEquals(scaled(weighing("a", 1, "b", -2)).form(),
                scaled(weighing("a", 3, "z", 0, "b", -6)).form());
        assertEquals(scaled(weighing("a", 1, "b", -2)).form(),
                scaled(weighing("b", -2, "a", 1)).form());
    }

    @Test
    void aSumOfNoWeightIsNoTerms() {
        assertInstanceOf(CanonicalForm.NoTerms.class, CanonicalForm.of(Map.<String, ExactRatio>of()));
        assertInstanceOf(CanonicalForm.NoTerms.class, CanonicalForm.of(weighing("a", 0, "b", 0)));
    }
}
