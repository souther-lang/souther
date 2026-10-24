package souther.compiler.abort;

import java.math.BigInteger;
import java.util.List;
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
     * @param answer how many elements the answer holds at most, of what the site is handed
     */
    record WhereTheAnswerFits(AnswerSize answer) implements GetsPast {

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

    /** How many elements an answer holds at most, in terms of what the site is handed. */
    sealed interface AnswerSize {

        /**
         * At most as many as the collections at {@code operands} hold together, and
         * {@code more} beside them.
         *
         * @param operands which of the site's operands, counted from nought
         * @param more     how many beside them
         */
        record SumOf(List<Integer> operands, int more) implements AnswerSize {

            public SumOf {
                operands = List.copyOf(operands);
                if (operands.isEmpty() && more == 0) {
                    throw new IllegalArgumentException("a sum of something");
                }
            }
        }

        /**
         * A piece for each element of the collection at {@code source}, each what the function
         * at {@code function} answers on that element, put end to end.
         */
        record PiecesOf(int source, int function) implements AnswerSize {}
    }
}
