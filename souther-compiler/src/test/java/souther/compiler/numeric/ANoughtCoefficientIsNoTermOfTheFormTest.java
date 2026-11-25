package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A form weighs no term at nought, however it was put together: a table of weights handed in by
 * hand with a nought in it is the form without that term, and so one value with every other
 * writing of the same form.
 */
class ANoughtCoefficientIsNoTermOfTheFormTest {

    @Test
    void aTermWeighedAtNoughtIsLeftOut() {
        Map<String, ExactRatio> weights = new LinkedHashMap<>();
        weights.put("x", ExactRatio.ZERO);
        weights.put("y", ExactRatio.of(2));

        LinearForm<String> form = new LinearForm<>(ExactRatio.ONE, weights);

        assertEquals(Map.of("y", ExactRatio.of(2)), form.coefs());
        assertEquals(LinearForm.atom("y").times(ExactRatio.of(2)).orNull()
                .plus(LinearForm.constant(ExactRatio.ONE)).orNull(), form);
    }

    @Test
    void aFormWhoseEveryTermIsAtNoughtIsItsConstant() {
        LinearForm<String> form = new LinearForm<>(ExactRatio.ZERO, Map.of("x", ExactRatio.ZERO));

        assertEquals(LinearForm.constant(ExactRatio.ZERO), form);
    }
}
