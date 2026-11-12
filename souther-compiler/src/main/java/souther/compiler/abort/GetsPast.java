package souther.compiler.abort;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawSubject;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

/**
 * Where working one site out answers a value, as against which reasons it may end a run for
 * ({@link AbortSet}).
 *
 * <p>Two questions about one site, answered by the same owners. Which reasons is what a reader
 * telling an author why a run stopped asks; this is what a reader asking whether some run gets past
 * the site asks, and the reasons alone do not say it: {@link AbortKind#REQUIRED_FORM_HAS_NO_PLACE}
 * is a sum past the end of an {@code Int} and a collection past what it holds, and only the
 * operation knows which, and of what.
 *
 * <p>Said only where the operation's own account of how it builds its answer says it. A site this
 * does not know of is {@link NotKnown}, which is not that it ends a run.
 */
public sealed interface GetsPast {

    /** It answers whatever it is handed. */
    record Always() implements GetsPast {}

    /**
     * It answers wherever the collection it answers holds no more elements than a collection holds
     * ({@link #MOST_ELEMENTS}), and ends a run for nothing else: it builds that collection
     * by putting elements in, so every collection it holds on the way holds no more than the
     * answer.
     *
     * <p>How many is a number of what the site is handed, in the words the library's laws count
     * with: how many an operand holds, and over the elements of an operand what each holds, or
     * what a closure among the operands answers on each.
     *
     * @param answer how many elements the answer holds at most, over the site's operands counted
     *               from nought
     */
    record WhereTheAnswerFits(LinearForm<LawNumber<Integer>> answer) implements GetsPast {

        public WhereTheAnswerFits {
            Objects.requireNonNull(answer, "an answer fits by some count");
        }
    }

    /**
     * It answers wherever the exact total of the {@code Int}s the list at {@code operand} holds is
     * an {@code Int}, and ends a run for nothing else: it adds them up exactly however far a total
     * on the way strays, and holds only the last to the type ({@code Lists.sumInt}). Not what a
     * sum of two answers, which is held to the type where it is worked out.
     *
     * @param operand which of the site's operands is the list, counted from nought
     */
    record WhereTheTotalFits(int operand) implements GetsPast {}

    /**
     * It answers wherever the exact product of the {@code Int}s the list at {@code operand} holds
     * is an {@code Int}, and ends a run for nothing else: it multiplies them exactly however far a
     * product on the way strays, and holds only the last to the type ({@code Lists.productInt}).
     * A nought among them makes the product nought. Not what a product of two answers, which is
     * held to the type where it is worked out.
     *
     * @param operand which of the site's operands is the list, counted from nought
     */
    record WhereTheProductFits(int operand) implements GetsPast {}

    /**
     * It answers wherever the whole numbers from the one at {@code from} to the one at {@code to},
     * both included, are no more than a collection holds ({@link #MOST_ELEMENTS}), and ends a run
     * for nothing else: it counts the span before it builds anything ({@code Capacity.span}), and
     * {@code from} above {@code to} answers the empty list.
     *
     * @param from which of the site's operands is the first number, counted from nought
     * @param to   which is the last
     */
    record WhereTheSpanFits(int from, int to) implements GetsPast {}

    /**
     * It answers wherever the {@code Int} at {@code dividend} is not the least an {@code Int} holds
     * or the one at {@code divisor} is not minus one, and ends a run for nothing else: a quotient
     * truncated toward nought lies no farther from nought than what it divides, but the least
     * {@code Int} divided by minus one is one past the greatest ({@code IntMath.divideExact}). A
     * divisor of nought answers a case.
     *
     * @param dividend which of the site's operands is the number divided, counted from nought
     * @param divisor  which is the number it is divided by
     */
    record WhereTheQuotientFits(int dividend, int divisor) implements GetsPast {}

    /**
     * It answers wherever the whole number it rounds the number at {@code operand} to is an
     * {@code Int}, and ends a run for nothing else ({@code IntNarrowing.rounded}). Whatever way it
     * is handed, that is the greatest whole number at most the number or the least at least it.
     *
     * @param operand which of the site's operands is the number rounded, counted from nought
     */
    record WhereTheRoundedNumberFits(int operand) implements GetsPast {}

    /**
     * It answers wherever the number at {@code operand}, where it is a whole number, is one an
     * {@code Int} holds, and ends a run for nothing else: a number that is not whole answers a
     * case before it is held to anything ({@code RationalMath.toWholeNumber}).
     *
     * @param operand which of the site's operands is the number, counted from nought
     */
    record WhereTheWholeNumberFits(int operand) implements GetsPast {}

    /**
     * It answers wherever the text it makes is no longer than a {@code String} holds, and ends a
     * run for nothing else: a case conversion of the text at {@code operand}, whose answer may
     * hold more code points than the text it was handed.
     *
     * @param operand which of the site's operands is the text, counted from nought
     */
    record WhereTheTextFits(int operand) implements GetsPast {}

    /** Nothing here says where it answers. */
    record NotKnown() implements GetsPast {}

    /**
     * How many elements a {@code List}, a {@code Map} or a {@code Set} holds at most (spec
     * §what-a-collection-holds): a number of the language, which a reasoning about a declaration
     * reads here and not from a backend's run time. The run time holds the same number, and
     * {@code TheCollectionBoundTheSpecificationStatesIsTheOneTheRuntimeHoldsTest} keeps the
     * specification, this and that one equal.
     */
    BigInteger MOST_ELEMENTS = BigInteger.valueOf(2_147_483_647L);

    /** How many the collections at {@code operands}, each a different one, hold together, and
     *  {@code more} beside them: what an answer put together of them and of {@code more}
     *  elements holds. */
    static LinearForm<LawNumber<Integer>> together(int more, Integer... operands) {
        Map<LawNumber<Integer>, ExactRatio> each = new LinkedHashMap<>();
        for (int at : operands) {
            if (each.put(new LawNumber.SizeOf<>(new LawSubject.Argument<>(at)), ExactRatio.ONE)
                    != null) {
                throw new IllegalArgumentException("operand " + at + " is counted once");
            }
        }
        return new LinearForm<>(ExactRatio.of(more), each);
    }
}
