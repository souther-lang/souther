package souther.compiler.semantics;

import souther.compiler.types.BinOp;
import souther.compiler.types.Type;

import java.util.List;

/**
 * Which arithmetic an operation of the language computes.
 *
 * <p>Which one it is, and not how a reader builds a value out of a call to it. What number
 * {@code Decimal.divide} answers is a fact about the operation; turning the four arguments of a
 * particular call into a term is the reading's, and lives with the reader that has the call.
 *
 * <p>What each argument has to be travels with the arithmetic, because a reader that took it from
 * anywhere else would be a second account of which argument is the divisor.
 */
public sealed interface Arithmetic {

    /**
     * What each argument has to be for this to be the operation's arithmetic, in the order the
     * operation takes them.
     *
     * <p>Read by position — the second one is what it divides by — so the positions are what a
     * declaration can drift out from under. A count alone does not catch it: an operation whose
     * scale and mode swapped places still takes four arguments, and what would change is only which
     * of them is read as the scale.
     */
    List<Reads> reads();

    /** Two numbers of the kind the operation answers, which is what all the arithmetic over a pair
     *  of them takes. */
    List<Reads> TWO_OF_ITS_OWN =
            List.of(Reads.THE_NUMBER_IT_ANSWERS, Reads.THE_NUMBER_IT_ANSWERS);

    /**
     * Arithmetic the language also writes as an operator.
     *
     * <p>The two reach one kernel in one argument order — {@code Int.add} is
     * {@code IntMath.addExact}, which is what {@code +} emits — so they compute one value and are
     * read as one term.
     */
    record TheOperator(BinOp op) implements Arithmetic {

        public TheOperator {
            java.util.Objects.requireNonNull(op, "this one names an operator");
        }

        @Override
        public List<Reads> reads() {
            return TWO_OF_ITS_OWN;
        }
    }

    /** A division of whole numbers truncated toward zero — the quotient {@code /} answers, reached
     *  where the divisor is one the model admits as zero. */
    record ATruncatingQuotient() implements Arithmetic {

        @Override
        public List<Reads> reads() {
            return TWO_OF_ITS_OWN;
        }
    }

    /** What that division leaves. The language writes no operator for it. */
    record ATruncatingRemainder() implements Arithmetic {

        @Override
        public List<Reads> reads() {
            return TWO_OF_ITS_OWN;
        }
    }

    /** A division of decimals rounded where the call says to round it. Not {@code /} over
     *  {@code Decimal}, which rounds at a significant-digit precision the run time sets. */
    record AQuotientRoundedToAScale() implements Arithmetic {

        @Override
        public List<Reads> reads() {
            return List.of(Reads.THE_NUMBER_IT_ANSWERS, Reads.THE_NUMBER_IT_ANSWERS,
                    Reads.A_SCALE, Reads.A_ROUNDING_MODE);
        }
    }

    /** What one argument of a numeric operation is, as far as a fact about it needs to know. */
    enum Reads {

        /** A number of the kind the operation answers. */
        THE_NUMBER_IT_ANSWERS,

        /** How many places the answer is rounded to, which is a count and so an {@code Int}. */
        A_SCALE,

        /** Which way it rounds there. */
        A_ROUNDING_MODE;

        /** Whether an argument declared {@code at} is this, for an operation answering
         *  {@code answered}. */
        public boolean heldBy(Type at, Type answered) {
            return switch (this) {
                case THE_NUMBER_IT_ANSWERS -> at.equals(answered);
                case A_SCALE -> at == Type.Prim.INT;
                case A_ROUNDING_MODE ->
                        at instanceof Type.Ref(souther.compiler.types.TypeSymbol name)
                                && name.module().equals(souther.compiler.types.TypeSymbol.RUNTIME)
                                && name.name().equals("RoundingMode");
            };
        }
    }
}
