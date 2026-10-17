package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A number a rule's statement is against is written beside its subject as the source would write a
 * number beside a value of the subject's type, and is not written where no such number says it.
 *
 * <p>The comparison is handed to the reading of any comparison, so what it is handed has to be one
 * that reading already reads: an Int literal beside an Int, a decimal beside a Decimal, and a decimal
 * read at its exact value beside a Rational.
 */
class AStatementIsHandedOnAsTheSourceWouldWriteItTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final ExactRatio A_HALF_BELOW_A_HUNDRED =
            ExactRatio.of(BigInteger.valueOf(199), BigInteger.TWO);

    private static final ExactRatio PAST_A_LONG =
            ExactRatio.of(BigInteger.valueOf(Long.MAX_VALUE).add(BigInteger.TEN));

    @Test
    void besideAnIntAWholeNumberAnIntSays() {
        Core subject = new Core.Int(1, Type.INT, POS);
        StatedComparison stated = ConstantComparison.stated(Rel.GE, subject, ExactRatio.of(100));
        assertEquals(new Core.Int(100, Type.INT, POS), stated.right());
        assertEquals(Core.BinaryReading.AS_THEY_STAND, stated.reading());
        assertNull(ConstantComparison.stated(Rel.GE, subject, A_HALF_BELOW_A_HUNDRED),
                "no Int is a half");
        assertNull(ConstantComparison.stated(Rel.GE, subject, PAST_A_LONG), "nor past a long");
    }

    @Test
    void besideADecimalADecimalOfAnySize() {
        Core subject = new Core.Decimal(BigDecimal.ONE, Type.DECIMAL, POS);
        StatedComparison half = ConstantComparison.stated(Rel.GE, subject, A_HALF_BELOW_A_HUNDRED);
        assertEquals(new Core.Decimal(new BigDecimal("99.5"), Type.DECIMAL, POS), half.right());
        assertEquals(Core.BinaryReading.AS_THEY_STAND, half.reading());
        assertEquals(0, new BigDecimal(BigInteger.valueOf(Long.MAX_VALUE).add(BigInteger.TEN))
                .compareTo(((Core.Decimal) ConstantComparison.stated(Rel.GE, subject, PAST_A_LONG)
                        .right()).value()));
    }

    @Test
    void besideARationalADecimalReadAtItsExactValue() {
        Core subject = new Core.Decimal(BigDecimal.ONE, Type.RATIONAL, POS);
        StatedComparison half = ConstantComparison.stated(Rel.GT, subject, A_HALF_BELOW_A_HUNDRED);
        assertEquals(new Core.Decimal(new BigDecimal("99.5"), Type.DECIMAL, POS), half.right());
        assertEquals(Core.BinaryReading.EXACT_NUMBERS, half.reading());
        assertNull(ConstantComparison.stated(Rel.GT, subject,
                ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3))), "no decimal is a third");
    }

    @Test
    void besideAnythingElseNothing() {
        assertNull(ConstantComparison.stated(Rel.GE, new Core.Str("a", Type.STRING, POS),
                ExactRatio.of(1)));
    }
}
