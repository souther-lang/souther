package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A form read as whole numbers: its constant and each weight, where each is a whole number the
 * host writes, and nothing where one is a part of one or is whole and has no place to be written
 * in. The last is the one a reader asking only whether the numbers are whole lets through.
 */
class AFormIsOverWholeNumbersOnlyWhereTheHostWritesEachTest {

    private static LinearForm<String> form(ExactRatio constant, ExactRatio x, ExactRatio y) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put("x", x);
        coefs.put("y", y);
        return new LinearForm<>(constant, coefs);
    }

    @Test
    void aFormOfWholeNumbersIsThoseNumbers() {
        WholeForm<String> whole = form(ExactRatio.of(-3), ExactRatio.of(6), ExactRatio.of(-4))
                .overWholeNumbers();
        assertEquals(BigInteger.valueOf(-3), whole.constant());
        assertEquals(BigInteger.valueOf(6), whole.weightOf("x"));
        assertEquals(BigInteger.valueOf(-4), whole.weightOf("y"));
        assertEquals(BigInteger.ZERO, whole.weightOf("z"));
        assertEquals(BigInteger.TWO, whole.step());
    }

    @Test
    void aPartOfOneAnywhereMakesItNone() {
        ExactRatio half = ExactRatio.of(1).dividedBy(ExactRatio.of(2)).orNull();
        assertNull(form(half, ExactRatio.ONE, ExactRatio.ONE).overWholeNumbers());
        assertNull(form(ExactRatio.ONE, ExactRatio.ONE, half).overWholeNumbers());
    }

    @Test
    void aWholeNumberNoHostWritesAnywhereMakesItNone() {
        ExactRatio unwritten = ExactRatio.tenTo(Long.MAX_VALUE);
        assertNull(form(unwritten, ExactRatio.ONE, ExactRatio.ONE).overWholeNumbers());
        assertNull(form(ExactRatio.ONE, unwritten, ExactRatio.ONE).overWholeNumbers());
    }
}
