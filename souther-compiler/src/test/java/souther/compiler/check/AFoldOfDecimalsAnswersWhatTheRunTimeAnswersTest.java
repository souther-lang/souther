package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.types.BinOp;
import souther.runtime.ConstraintViolation;
import souther.runtime.DecimalMath;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Optional;
import java.util.function.BinaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the compiler folds of two {@code Decimal} constants is what the program computes of them
 * when it runs: the same value, or nothing where the run time aborts.
 *
 * <p>The pairs are put at the ends of the scale range and on both sides of a nought, because that
 * is where {@code BigDecimal} and the language part: a nought factor on the left is multiplied at
 * a scale moved back into range, and the same factor on the right is refused.
 */
class AFoldOfDecimalsAnswersWhatTheRunTimeAnswersTest {

    private static BigDecimal of(long unscaled, int scale) {
        return new BigDecimal(BigInteger.valueOf(unscaled), scale);
    }

    private static final List<BigDecimal> DECIMALS = List.of(
            of(0, 0), of(0, 1), of(0, 1 << 30), of(0, Integer.MAX_VALUE), of(0, Integer.MIN_VALUE),
            of(1, 0), of(1, 1), of(1, 1 << 30), of(1, (1 << 30) + 1), of(1, Integer.MAX_VALUE),
            of(1, Integer.MIN_VALUE), of(-3, -(1 << 30)), of(25, 2));

    @Test
    void aProductIsFoldedWhereTheRunTimeAnswersIt() {
        agree(BinOp.MUL, DecimalMath::multiply);
    }

    @Test
    void aSumIsFoldedWhereTheRunTimeAnswersIt() {
        agree(BinOp.ADD, DecimalMath::add);
    }

    @Test
    void aDifferenceIsFoldedWhereTheRunTimeAnswersIt() {
        agree(BinOp.SUB, DecimalMath::subtract);
    }

    private static void agree(BinOp op, BinaryOperator<BigDecimal> runTime) {
        int refused = 0;
        for (BigDecimal a : DECIMALS) {
            for (BigDecimal b : DECIMALS) {
                if (op != BinOp.MUL && (Math.abs((long) a.scale() - b.scale()) > 1 << 20
                        && a.signum() != 0 && b.signum() != 0)) {
                    continue;   // a sum at such a distance allocates the digits between the two
                }
                Optional<Object> folded = ConstantAlgebra.binary(op, a, b);
                BigDecimal ran = null;
                try {
                    ran = runTime.apply(a, b);
                } catch (ConstraintViolation _) {
                    refused++;
                }
                String pair = op + " " + a + " " + b;
                if (ran == null) {
                    assertTrue(folded.isEmpty(), "the run time aborts and the fold answers: " + pair);
                } else {
                    assertEquals(0, ran.compareTo((BigDecimal) folded.orElseThrow()), pair);
                    assertEquals(ran.scale(), ((BigDecimal) folded.orElseThrow()).scale(), pair);
                }
            }
        }
        assertTrue(op != BinOp.MUL || refused > 0, "the pairs include some the run time refuses");
    }
}
