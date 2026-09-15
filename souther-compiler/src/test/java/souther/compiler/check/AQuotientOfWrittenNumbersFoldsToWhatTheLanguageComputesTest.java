package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;
import souther.runtime.ConstraintViolation;
import souther.runtime.IntMath;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a divide of two written numbers comes to at compile time.
 *
 * <p>A whole-number divide by a divisor written down is the truncating quotient the language
 * defines, and this computes it as it computes a sum or a product. What it declines is what a value
 * handed back would be wrong about: a divisor of nought, which the run time aborts on; the quotient
 * whose value is outside the range an {@code Int} holds, which aborts there too while {@code long}
 * division quietly answers the dividend; and a {@code Decimal} divide, whose answer is rounded at a
 * scale this does not hold.
 *
 * <p>Each refusal is written beside the case it differs from by one part, so that a fold answering
 * everything and a fold answering nothing are told apart here rather than at the reader.
 */
class AQuotientOfWrittenNumbersFoldsToWhatTheLanguageComputesTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Optional<Object> fold(BinOp op, Hir.Expr left, Hir.Expr right) {
        return ConstEval.against(Symbols.none(DefaultStdlib.get())).eval(
                new Hir.Binary(op, left, right,
                        SourceConstructOrigin.written(new WrittenOwner.Body("m", "b"), 0,
                                SourceConstruct.BINARY),
                        POS, null));
    }

    private static Optional<Object> whole(long dividend, long divisor) {
        return fold(BinOp.DIV, new Hir.IntLit(dividend, POS, null),
                new Hir.IntLit(divisor, POS, null));
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
     * The one whole-number quotient whose value is outside the range an {@code Int} holds. An
     * {@code Int} that overflows aborts rather than wrapping, and {@code long} division answers the
     * dividend, so a fold that handed that back would be answering for an expression the run time
     * refuses to compute.
     */
    @Test
    void theQuotientOutsideTheRangeAnIntHoldsIsDeclined() {
        assertEquals(Optional.empty(), whole(Long.MIN_VALUE, -1));
        assertEquals(Optional.of(Long.MIN_VALUE), whole(Long.MIN_VALUE, 1));
        assertEquals(Optional.of(-Long.MAX_VALUE), whole(Long.MAX_VALUE, -1));
    }

    /**
     * The fold answers where the operator computes a value and declines where it aborts, which is
     * the whole of what it is allowed to do.
     *
     * <p>Held against the run time itself rather than against a table written here a second time:
     * what a whole-number divide comes to is {@code IntMath.divideExact}'s to say, and a fold that
     * answered something else would be a compile-time value for an expression the program refuses
     * to compute. Both sides of every pair are read before anything is asserted, so a disagreement
     * names the pair it is about.
     */
    @Test
    void theFoldAnswersWhereTheOperatorDoesAndDeclinesWhereItAborts() {
        long[][] pairs = {{7, 2}, {8, 2}, {-3, 2}, {3, -2}, {7, 1}, {7, 0},
                {Long.MIN_VALUE, -1}, {Long.MIN_VALUE, 1}, {Long.MAX_VALUE, -1}};
        List<String> computed = new ArrayList<>();
        List<String> folded = new ArrayList<>();
        for (long[] pair : pairs) {
            String written = pair[0] + " / " + pair[1] + ": ";
            computed.add(written + run(pair[0], pair[1]));
            folded.add(written + whole(pair[0], pair[1]).orElse("aborts"));
        }

        assertEquals(computed, folded);
    }

    /** What the operator answers for these two, or the word for its aborting. */
    private static Object run(long dividend, long divisor) {
        try {
            return IntMath.divideExact(dividend, divisor);
        } catch (ConstraintViolation _) {
            return "aborts";
        }
    }

    /**
     * A {@code Decimal} divide is rounded at a scale the run time sets and this does not hold, so
     * it stays the run time's to answer.
     *
     * <p>Beside a {@code Decimal} the fold does answer for, so what is read here is the divide and
     * not the kind of number it was written over. Held by amount rather than by how the product is
     * spelled, which is how a {@code Decimal} is compared everywhere else.
     */
    @Test
    void aDecimalDivideIsLeftToTheRunTime() {
        Hir.Expr seven = new Hir.DecimalLit(new BigDecimal("7.0"), POS, null);
        Hir.Expr two = new Hir.DecimalLit(new BigDecimal("2.0"), POS, null);

        assertEquals(Optional.empty(), fold(BinOp.DIV, seven, two));
        assertEquals(0, ((BigDecimal) fold(BinOp.MUL, seven, two).orElseThrow())
                .compareTo(new BigDecimal("14")));
    }
}
