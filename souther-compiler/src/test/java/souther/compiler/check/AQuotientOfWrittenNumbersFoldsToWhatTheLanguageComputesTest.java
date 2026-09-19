package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;
import souther.compiler.numeric.ExactRatio;
import souther.runtime.ConstraintViolation;
import souther.runtime.RationalMath;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
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

    /**
     * The same number written two ways: the minus outside the quotient, and inside it on the
     * dividend.
     *
     * <p>Asked because the second folds through the whole numbers and the first through the ratio, so
     * a fold that read one and not the other would make a constant of a number for the way it was
     * bracketed. What reads a form of these later is the affine walk, and it reads a name given
     * either.
     */
    @Test
    void theNegationOfAQuotientFoldsWhereverTheMinusWasWritten() {
        Optional<Object> outside = ConstEval.against(Symbols.none(DefaultStdlib.get())).eval(
                new Hir.Neg(new Hir.Binary(BinOp.DIV, new Hir.IntLit(1, POS, null),
                        new Hir.IntLit(2, POS, null),
                        SourceConstructOrigin.written(new WrittenOwner.Body("m", "b"), 0,
                                SourceConstruct.BINARY),
                        POS, null), POS, null));

        assertEquals(ratio(-1, 2), outside);
        assertEquals(outside, whole(-1, 2), "one number, whichever side the minus was written on");
    }

    private static Optional<Object> whole(long dividend, long divisor) {
        return fold(BinOp.DIV, new Hir.IntLit(dividend, POS, null),
                new Hir.IntLit(divisor, POS, null));
    }

    private static Optional<Object> ratio(long numerator, long denominator) {
        return Optional.of(ExactRatio.of(BigInteger.valueOf(numerator),
                BigInteger.valueOf(denominator)));
    }

    @Test
    void aWholeNumberQuotientIsTheExactOneTheLanguageComputes() {
        assertEquals(ratio(7, 2), whole(7, 2));
        assertEquals(ratio(4, 1), whole(8, 2));
    }

    /**
     * Nothing is rounded either way, which is what the exact quotient is for. Two pairs whose
     * truncating quotients agree and whose exact ones do not are what says so.
     */
    @Test
    void aNegativeQuotientIsNeitherTruncatedNorFloored() {
        assertEquals(ratio(-3, 2), whole(-3, 2));
        assertEquals(ratio(-3, 2), whole(3, -2));
    }

    /** Nothing is divided by nought, and the fold says so by answering nothing rather than by
     *  answering. */
    @Test
    void aDivisorOfNoughtIsDeclined() {
        assertEquals(Optional.empty(), whole(7, 0));
        assertEquals(ratio(7, 1), whole(7, 1));
    }

    /**
     * No pair is declined for the size of its quotient. The one whose truncating quotient no
     * {@code Int} held is the pair that made this a rule, and its exact quotient is a whole number
     * the ratio holds — so the refusal that stood here is gone with the operator's truncation.
     */
    @Test
    void noPairIsDeclinedForTheSizeOfItsQuotient() {
        assertEquals(ratio(Long.MIN_VALUE, -1), whole(Long.MIN_VALUE, -1));
        assertEquals(ratio(Long.MIN_VALUE, 1), whole(Long.MIN_VALUE, 1));
        assertEquals(ratio(Long.MAX_VALUE, -1), whole(Long.MAX_VALUE, -1));
    }

    /**
     * The fold answers where the operator computes a value and declines where it aborts, which is
     * the whole of what it is allowed to do.
     *
     * <p>Held against the run time itself rather than against a table written here a second time:
     * what a whole-number divide comes to is {@code RationalMath.divideWholeNumbers}'s to say, and a
     * fold that answered something else would be a compile-time value for an expression the program
     * computes differently. The two hold the exact value in types of their own — one reasons in it and
     * one carries it (ADR-0117) — and both spell a ratio the same way, which is what is compared.
     * Both sides of every pair are read before anything is asserted, so a disagreement names the pair
     * it is about.
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
            return RationalMath.divideWholeNumbers(dividend, divisor);
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
