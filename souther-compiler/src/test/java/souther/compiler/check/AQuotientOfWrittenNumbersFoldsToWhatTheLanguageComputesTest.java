package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a divide of two written numbers comes to at compile time.
 *
 * <p>A whole-number divide by a divisor written down is the truncating quotient the language
 * defines, and this computes it as it computes a sum or a product. What it declines are the three
 * where a value handed back would be one the run time does not compute: a divisor of nought, which
 * aborts; the one quotient of two whole numbers that is not a whole number, which overflows and
 * aborts where {@code long} division quietly answers the dividend; and a {@code Decimal} divide,
 * whose answer is rounded at a scale this does not hold.
 *
 * <p>Each refusal is written beside the case it differs from by one part, so that a fold answering
 * everything and a fold answering nothing are told apart here rather than at the reader.
 */
class AQuotientOfWrittenNumbersFoldsToWhatTheLanguageComputesTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Optional<Object> fold(Hir.Expr left, Hir.Expr right) {
        return ConstEval.against(Symbols.none(DefaultStdlib.get())).eval(
                new Hir.Binary(BinOp.DIV, left, right,
                        SourceConstructOrigin.written(new WrittenOwner.Body("m", "b"), 0,
                                SourceConstruct.BINARY),
                        POS, null));
    }

    private static Optional<Object> whole(long dividend, long divisor) {
        return fold(written(dividend), written(divisor));
    }

    /** A written whole number, with a minus in front of it where it is below nought. */
    private static Hir.Expr written(long value) {
        return value < 0
                ? new Hir.Neg(new Hir.IntLit(-value, POS, null), POS, null)
                : new Hir.IntLit(value, POS, null);
    }

    @Test
    void aWholeNumberQuotientIsTheOneTheLanguageComputes() {
        assertEquals(Optional.of(3L), whole(7, 2));
        assertEquals(Optional.of(4L), whole(8, 2));
    }

    /**
     * Toward nought and not toward the lesser number, which is what the language says a whole-number
     * divide does. The two answers differ by one here, so a fold that floored would be read off this
     * and not off a case where the rounding makes no difference.
     */
    @Test
    void aNegativeQuotientIsTruncatedTowardNought() {
        assertEquals(Optional.of(-1L), whole(-3, 2));
        assertEquals(Optional.of(-1L), whole(3, -2));
    }

    /** Nothing is divided by nought, and the fold says so by answering nothing rather than by
     *  answering. */
    @Test
    void aDivisorOfNoughtIsDeclined() {
        assertEquals(Optional.empty(), whole(7, 0));
        assertEquals(Optional.of(7L), whole(7, 1));
    }

    /**
     * The one quotient of two whole numbers that is not one. An {@code Int} that overflows aborts
     * rather than wrapping, and {@code long} division answers the dividend, so a fold that handed
     * that back would be answering for an expression the run time refuses to compute.
     */
    @Test
    void theQuotientOutsideTheRangeAnIntHoldsIsDeclined() {
        assertEquals(Optional.empty(), whole(Long.MIN_VALUE, -1));
        assertEquals(Optional.of(Long.MIN_VALUE), whole(Long.MIN_VALUE, 1));
        assertEquals(Optional.of(Long.MAX_VALUE * -1), whole(Long.MAX_VALUE, -1));
    }

    /** A {@code Decimal} divide is rounded at a scale the run time sets and this does not hold, so
     *  it stays the run time's to answer. */
    @Test
    void aDecimalDivideIsLeftToTheRunTime() {
        Hir.Expr seven = new Hir.DecimalLit(new BigDecimal("7.0"), POS, null);
        Hir.Expr two = new Hir.DecimalLit(new BigDecimal("2.0"), POS, null);

        assertEquals(Optional.empty(), fold(seven, two));
        assertEquals(Optional.of(new BigDecimal("14.00")),
                ConstEval.against(Symbols.none(DefaultStdlib.get())).eval(
                        new Hir.Binary(BinOp.MUL, seven, two,
                                SourceConstructOrigin.written(new WrittenOwner.Body("m", "b"), 0,
                                        SourceConstruct.BINARY),
                                POS, null)));
    }
}
