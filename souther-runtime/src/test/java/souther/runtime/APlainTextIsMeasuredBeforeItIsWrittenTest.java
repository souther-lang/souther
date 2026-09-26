package souther.runtime;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * {@code String.fromDecimal} decides whether a value's plain notation has a place from its length,
 * worked out before the text is, so the length it works out has to be the length of the text it
 * would write. Held against {@code toPlainString} itself on values of every shape the formula
 * separates: nought and not, either sign, a scale below, at and above nought, and a scale above,
 * at and below the precision.
 */
class APlainTextIsMeasuredBeforeItIsWrittenTest {

    static Stream<BigDecimal> values() {
        Stream.Builder<BigDecimal> out = Stream.builder();
        for (long unscaled : new long[] {0, 1, -1, 7, -7, 12, -12, 1234, -1234, 100, -100}) {
            for (int scale = -6; scale <= 6; scale++) {
                out.add(new BigDecimal(BigInteger.valueOf(unscaled), scale));
            }
        }
        return out.build();
    }

    @ParameterizedTest
    @MethodSource("values")
    void theLengthIsTheLengthOfTheText(BigDecimal d) {
        assertEquals(d.toPlainString().length(), DecimalMath.plainTextLength(d),
                () -> "(" + d.unscaledValue() + ", " + d.scale() + ") is \"" + d.toPlainString() + "\"");
    }

    /** At the ends of the scale range the length is past what a {@code String} holds, and that is
     *  what is answered — without the text being asked for. */
    @Test
    void aTextNoStringHoldsAbortsBeforeItIsWritten() {
        for (int scale : new int[] {Integer.MIN_VALUE, Integer.MIN_VALUE + 1, Integer.MAX_VALUE}) {
            BigDecimal d = new BigDecimal(BigInteger.ONE, scale);
            assertThrows(ConstraintViolation.class, () -> Strings.fromDecimal(d), () -> "scale " + scale);
        }
    }

    /** Nought is {@code "0"} at every scale up to zero, including the floor. */
    @Test
    void noughtAtTheFloorIsOneChar() {
        assertEquals("0", Strings.fromDecimal(new BigDecimal(BigInteger.ZERO, Integer.MIN_VALUE)));
    }
}
