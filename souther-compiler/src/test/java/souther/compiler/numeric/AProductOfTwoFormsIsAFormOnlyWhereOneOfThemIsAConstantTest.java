package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Two forms multiplied: the other scaled where one of them is a constant, from either side, and no
 * form at all where both weigh an atom.
 */
class AProductOfTwoFormsIsAFormOnlyWhereOneOfThemIsAConstantTest {

    private static final LinearForm<String> TWO_X_PLUS_ONE =
            new LinearForm<>(ExactRatio.ONE, Map.of("x", ExactRatio.of(2)));
    private static final LinearForm<String> THREE = LinearForm.constant(ExactRatio.of(3));
    private static final LinearForm<String> SIX_X_PLUS_THREE =
            new LinearForm<>(ExactRatio.of(3), Map.of("x", ExactRatio.of(6)));

    @Test
    void aConstantScalesTheOtherFromEitherSide() {
        assertEquals(SIX_X_PLUS_THREE, THREE.productWith(TWO_X_PLUS_ONE).orNull());
        assertEquals(SIX_X_PLUS_THREE, TWO_X_PLUS_ONE.productWith(THREE).orNull());
        assertEquals(LinearForm.constant(ExactRatio.of(9)), THREE.productWith(THREE).orNull());
    }

    @Test
    void twoFormsWeighingAnAtomMakeNoForm() {
        assertNull(TWO_X_PLUS_ONE.productWith(TWO_X_PLUS_ONE));
        assertNull(TWO_X_PLUS_ONE.productWith(LinearForm.atom("y")));
    }
}
