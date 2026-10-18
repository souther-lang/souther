package souther.compiler.semantics;

import souther.compiler.types.BinOp;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.List;

/**
 * On which operands an operator of the language answers a value, and on which a run stops at it.
 *
 * <p>A fact about the operator and its type, and not about a site. Which reasons a run may stop for
 * at a place is {@link souther.compiler.abort.AbortSites}' — that is a classification of endings,
 * and says nothing of the operands. This says the operands: {@code a + 1} over {@code Int} answers
 * exactly where {@code a + 1}, worked out over the whole numbers, is a number an {@code Int} holds,
 * and so where {@code a} is below the greatest {@code Int}. A reader that asks whether a run gets
 * past the sum reads it here, and the two readers that ask — what holds once a value was worked
 * out, and what a statement says where the operations it is read through answer — read it once.
 *
 * <p>Worked out over the whole numbers, never over what an {@code Int} wraps to: a sum compared
 * after it was held would be inside what an {@code Int} holds whatever the operands were.
 *
 * <p><b>Not stated is not everywhere.</b> {@link NotStated} is an operator that stops a run on some
 * operands this compiler writes no region for — a {@code Decimal} sum whose digits or scale no
 * value has room for, a quotient of a {@code Rational} whose exponent leaves what one holds. A
 * reader holding it knows a run may stop there and does not know where, which is neither a run
 * that always gets past nor one that never does.
 */
public sealed interface WhereAnOperatorAnswers {

    /** On every operand: the operator ends no run. */
    record Everywhere() implements WhereAnOperatorAnswers {}

    /**
     * Where its value, worked out exactly, lies from {@code least} to {@code greatest}: what an
     * {@code Int} sum, difference, product or negation answers is that number where an {@code Int}
     * holds it, and nothing elsewhere.
     */
    record WhereItsExactValueIsHeld(BigInteger least, BigInteger greatest)
            implements WhereAnOperatorAnswers {

        public WhereItsExactValueIsHeld {
            if (least.compareTo(greatest) > 0) {
                throw new IllegalArgumentException("a type holds the numbers between two ends");
            }
        }
    }

    /**
     * Where the divisor is not nought: a quotient of two whole numbers or two decimals is a
     * {@code Rational} made fresh from them, which has room for it, so nought is the one divisor it
     * has no answer for.
     */
    record WhereTheDivisorIsNotNought() implements WhereAnOperatorAnswers {}

    /**
     * On some operands and not on others, which this compiler writes no region for.
     *
     * @param why what the region would have to say that nothing here says
     */
    record NotStated(String why) implements WhereAnOperatorAnswers {}

    /** What every whole number an {@code Int} holds lies between. */
    WhereItsExactValueIsHeld WHAT_AN_INT_HOLDS = new WhereItsExactValueIsHeld(
            BigInteger.valueOf(Long.MIN_VALUE), BigInteger.valueOf(Long.MAX_VALUE));

    /**
     * Where {@code op} over operands of {@code operands} answering {@code answer} answers.
     *
     * <p>Read off the types as {@link souther.compiler.abort.AbortSites} reads them: an
     * {@code Int + Int} answers {@code Int}, and an answer of {@code Rational} is worked out as a
     * {@code Rational} whatever the operands were. A quotient is the one place the operands decide
     * it — every quotient answers {@code Rational}, and only one with a {@code Rational} operand
     * carries an exponent it may have no room for.
     */
    static WhereAnOperatorAnswers ofAnOperator(BinOp op, Type answer, List<Type> operands) {
        return switch (op) {
            case EQ, NE, LT, LE, GT, GE, AND, OR -> new Everywhere();
            case ADD, SUB, MUL -> answer == Type.INT ? WHAT_AN_INT_HOLDS
                    : new NotStated("where a " + Type.show(answer)
                            + " has room for a sum, a difference or a product");
            case DIV -> operands.contains(Type.RATIONAL)
                    ? new NotStated("where a quotient of a Rational has room for its exponent")
                    : new WhereTheDivisorIsNotNought();
            case CONCAT -> new NotStated("where what a join answers is no longer than its type"
                    + " holds");
        };
    }

    /**
     * Where a negation answering {@code answer} answers: an {@code Int} has no negation of the least
     * of them, and a {@code Decimal} or a {@code Rational} only changes its sign.
     */
    static WhereAnOperatorAnswers ofANegation(Type answer) {
        return answer == Type.INT ? WHAT_AN_INT_HOLDS : new Everywhere();
    }
}
