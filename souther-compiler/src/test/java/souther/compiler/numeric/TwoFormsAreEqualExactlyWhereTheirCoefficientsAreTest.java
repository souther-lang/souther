package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Whether two forms are one form is a question about their coefficients and nothing else: the hash
 * a form holds to answer it quickly gives the same answer as comparing the maps, and the order the
 * coefficients were handed over in is not part of it.
 */
class TwoFormsAreEqualExactlyWhereTheirCoefficientsAreTest {

    private static CanonicalForm<String> of(Object... atomsAndWeights) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        for (int at = 0; at < atomsAndWeights.length; at += 2) {
            coefs.put((String) atomsAndWeights[at], ExactRatio.of((Integer) atomsAndWeights[at + 1]));
        }
        return new CanonicalForm<>(coefs);
    }

    @Test
    void formsWrittenInAnotherOrderAreOneFormWithOneHash() {
        CanonicalForm<String> ab = of("a", 1, "b", 2);
        CanonicalForm<String> ba = of("b", 2, "a", 1);

        assertEquals(ab, ba);
        assertEquals(ba, ab);
        assertEquals(ab.hashCode(), ba.hashCode());
    }

    @Test
    void formsThatDifferInAWeightAPositionOrAFirstAskedHashAreNotEqual() {
        CanonicalForm<String> form = of("a", 1, "b", 2);

        assertNotEquals(form, of("a", 1, "b", 3));
        assertNotEquals(form, of("a", 1, "c", 2));
        assertNotEquals(form, of("a", 1));
        assertNotEquals(form, of("a", -1, "b", -2));
        assertFalse(form.equals(null));
        assertFalse(form.equals("a + 2b"));
    }

    @Test
    void askingTheHashBeforeOrAfterComparingChangesNothing() {
        CanonicalForm<String> asked = of("a", 1, "b", 2);
        int hash = asked.hashCode();
        CanonicalForm<String> unasked = of("a", 1, "b", 2);

        assertEquals(asked, unasked);
        assertEquals(hash, unasked.hashCode());
    }
}
