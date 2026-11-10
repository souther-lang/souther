package souther.compiler.abort;

import souther.compiler.types.BinOp;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawSubject;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
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
     * It answers wherever the text it makes is no longer than a {@code String} holds, and ends a
     * run for nothing else: a case conversion of the text at {@code operand}, whose answer may
     * hold more code points than the text it was handed.
     *
     * @param operand which of the site's operands is the text, counted from nought
     */
    record WhereTheTextFits(int operand) implements GetsPast {}

    /**
     * It answers wherever every one of {@code rooms} has room, and ends a run for nothing else: an
     * operation that has no room for the digits or the scale of its answer ends the run. A single
     * operation asks one, and a body that works several decimals out asks each of the operations
     * it does.
     *
     * <p>Which scales a run is at is not said here: it turns on what the arguments are, which a
     * reader of a run reads off them.
     *
     * @param rooms  what each operation the call works out asks, over what the call is handed
     * @param answer the shape the call answers with, over the same: a number's, never the scale
     *               asked for alone, which has no digits to say
     */
    record WhereTheScalesHaveRoom(List<Room> rooms, ScaleBound answer) implements GetsPast {

        public WhereTheScalesHaveRoom {
            rooms = List.copyOf(rooms);
            if (saysOnlyAScale(answer)) {
                throw new IllegalArgumentException(
                        "an answer is a number's shape, and a scale asked for has no digits: "
                                + answer);
            }
        }

        private static boolean saysOnlyAScale(ScaleBound bound) {
            return switch (bound) {
                case ScaleBound.WrittenAt _ -> true;
                case ScaleBound.Larger(var one, var other) ->
                        saysOnlyAScale(one) || saysOnlyAScale(other);
                default -> false;
            };
        }

        /** What one operation asks: that the scales of two numbers leave it room under
         *  {@code law}. */
        public record Room(ScaleLaw law, ScaleBound first, ScaleBound second) {}

        /** A sum, a difference or a product of the two arguments. */
        public static WhereTheScalesHaveRoom ofTheOperator(BinOp op) {
            ScaleLaw law = new ScaleLaw.OfTheOperator(op);
            ScaleBound first = new ScaleBound.Argument(0);
            ScaleBound second = new ScaleBound.Argument(1);
            return new WhereTheScalesHaveRoom(List.of(new Room(law, first, second)),
                    new ScaleBound.Left(law, first, second));
        }

        /**
         * A quotient asked for at the places the call writes out at {@code scaleAt}, of the
         * numbers at {@code dividendAt} and {@code divisorAt}: the run works at the scale asked
         * and the larger of the two it divides, and the answer, where it is a number, is of the
         * shape that law leaves: at the scale asked, and of the digits the numbers it is worked
         * out of give it. A divisor of nought is no stop here: it is a case the call answers.
         */
        public static WhereTheScalesHaveRoom ofADivision(int dividendAt, int divisorAt,
                                                         int scaleAt) {
            ScaleLaw law = new ScaleLaw.Asked();
            ScaleBound asked = new ScaleBound.WrittenAt(scaleAt);
            ScaleBound worked = new ScaleBound.Larger(new ScaleBound.Argument(dividendAt),
                    new ScaleBound.Argument(divisorAt));
            return new WhereTheScalesHaveRoom(List.of(new Room(law, asked, worked)),
                    new ScaleBound.Left(law, asked, worked));
        }

        /** A number rounded to the places the call writes out at {@code scaleAt}, of the number
         *  at {@code operandAt}. */
        public static WhereTheScalesHaveRoom ofARounding(int scaleAt, int operandAt) {
            ScaleLaw law = new ScaleLaw.Asked();
            ScaleBound first = new ScaleBound.WrittenAt(scaleAt);
            ScaleBound second = new ScaleBound.Argument(operandAt);
            return new WhereTheScalesHaveRoom(List.of(new Room(law, first, second)),
                    new ScaleBound.Left(law, first, second));
        }
    }

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
