package souther.compiler.semantics;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.types.BinOp;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Optional;

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

    /**
     * The operator the language writes this arithmetic as, or null where it writes none.
     *
     * <p>Declared with the arithmetic because it is a fact about which arithmetic it is: what
     * {@code +} computes over whole numbers is what {@code Int.add} answers, and a reader holding
     * the operator and wanting the operation that owns the account is asking exactly this. Kept
     * anywhere else, which operation an operator reaches would be a second list beside the one the
     * declarations already are.
     *
     * <p>Not every arithmetic has one. A remainder is written as a call only, and so are the two
     * quotients that name how their fraction goes — what {@code /} answers is exact, and an
     * operation that truncates or rounds is a different number from the one the operator computes.
     * What an operator names is the arithmetic and not the operation: two operations computing one
     * arithmetic are two the operator reaches, and a reader that needs one of them has nothing here
     * to pick with.
     */
    default BinOp writtenAs() {
        return null;
    }

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

        /**
         * Which operators a row may state, said here rather than trusted of the rows.
         *
         * <p>What this declares is that a library operation computes what an operator computes,
         * and every reader of it takes the operation to answer a number. A row naming an operator
         * that answers something else would put that operation's value where a number is read.
         */
        public TheOperator {
            java.util.Objects.requireNonNull(op, "this one names an operator");
            if (!op.answersANumber()) {
                throw new IllegalArgumentException(
                        "an operation computing what an operator computes answers a number: " + op);
            }
        }

        @Override
        public List<Reads> reads() {
            return TWO_OF_ITS_OWN;
        }

        @Override
        public BinOp writtenAs() {
            return op;
        }
    }

    /** A division of whole numbers truncated toward zero, answered in the case carrying a number
     *  and not where the divisor is one the model admits as zero. Written as a call: the operator's
     *  quotient is exact, and this is the number a model asks for when it says where the fraction
     *  goes. */
    record ATruncatingQuotient() implements Arithmetic {

        @Override
        public List<Reads> reads() {
            return TWO_OF_ITS_OWN;
        }

        /**
         * Which of the numbers it reads is the one it divides by, which is the second of them.
         *
         * <p>Said here because it is a fact about this arithmetic and nowhere else is. What each
         * argument has to be travels with the arithmetic and is read by position (above), so which
         * position is the divisor is the same statement one step further in — and a reader working
         * it out from something beside the arithmetic would be answering it from a place that has
         * no say.
         */
        public int divisor() {
            return 1;
        }

        /**
         * What dividing {@code value} by {@code by} answers: the whole number left by truncating
         * toward zero.
         *
         * <p><b>Here because it is this arithmetic's own answer, and every direction reads it.</b>
         * Reading a row's value off an observation and solving for a value that answers a number
         * are the same division asked twice, and a second spelling of "toward zero" is two
         * roundings somebody keeps in step by hand — which is a row offered at a number it reads
         * back as something else, the day they part.
         *
         * <p>Said of the arithmetic rather than of the account that takes it. Which numbers an
         * operation's answer names and which of its arguments is the divisor are the account's;
         * what the operator computes is written down once, here, where the operator is named.
         *
         * <p>Divided as numbers, so the answer is the whole number the operator computes whatever
         * places either was written to. An observation is read as a count of whatever scale it
         * came with, and a quotient of two decimals far apart in scale can be a whole number no
         * host holds — which is said, with which way, rather than let the decimal division throw.
         */
        public static ExactAnswer<BigDecimal> quotientOf(BigDecimal value, BigDecimal by) {
            if (by.signum() == 0) {
                throw new IllegalArgumentException(
                        "a truncating quotient's divisor of nought is refused where the term is"
                                + " made, and is never one this reads");
            }
            return switch (ExactRatio.of(value).dividedBy(ExactRatio.of(by))
                    .flatMap(ExactRatio::truncated)) {
                case ExactAnswer.Held<BigInteger> held ->
                        ExactAnswer.held(new BigDecimal(held.value()));
                case ExactAnswer.Unheld<BigInteger> unheld -> ExactAnswer.unheld(unheld.why());
            };
        }
    }

    /** What that division leaves. The language writes no operator for it. */
    record ATruncatingRemainder() implements Arithmetic {

        @Override
        public List<Reads> reads() {
            return TWO_OF_ITS_OWN;
        }
    }

    /**
     * What a division of whole numbers leaves where its quotient is floored, which takes the sign of
     * the divisor. Answered directly: a divisor of nought aborts rather than coming back as a case.
     */
    record AFloorRemainder() implements Arithmetic {

        @Override
        public List<Reads> reads() {
            return TWO_OF_ITS_OWN;
        }

        /** Which of the numbers it reads is the one it divides by, which is the second of them. */
        public int divisor() {
            return 1;
        }

        /**
         * What is left of {@code value} divided by {@code by}: {@code value - by * floor(value / by)}.
         *
         * <p>Here because it is this arithmetic's own answer, and every direction reads it: a row's
         * remainder read off an observation and a value written for a remainder are the same
         * division asked twice. The answer is one whole number from nought up to the divisor, not
         * reaching it, where the divisor is above nought, and from the divisor up to nought, not
         * reaching it, where it is below. Divided as numbers, so a pair far apart in scale is a
         * whole number said with which way it was not held rather than a throw.
         */
        public static ExactAnswer<BigDecimal> remainderOf(BigDecimal value, BigDecimal by) {
            if (by.signum() == 0) {
                throw new IllegalArgumentException(
                        "a floor remainder's divisor of nought is refused where the term is made,"
                                + " and is never one this reads");
            }
            ExactRatio dividend = ExactRatio.of(value);
            ExactRatio divisor = ExactRatio.of(by);
            ExactAnswer<Optional<BigDecimal>> left = dividend.dividedBy(divisor)
                    .flatMap(ExactRatio::floor)
                    .flatMap(floor -> divisor.times(ExactRatio.of(floor)))
                    .flatMap(product -> dividend.minus(product))
                    .flatMap(ExactRatio::writtenDecimal);
            return switch (left) {
                case ExactAnswer.Held<Optional<BigDecimal>> held -> held.value().isPresent()
                        ? ExactAnswer.held(held.value().get())
                        : ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS);
                case ExactAnswer.Unheld<Optional<BigDecimal>> unheld ->
                        ExactAnswer.unheld(unheld.why());
            };
        }

        /**
         * {@code divisor} where it is a whole number other than nought, with its sign, or null where
         * it is none: a divisor that is not one names no residue class, and nought is a call that
         * aborts.
         *
         * <p>The sign is part of the answer, because the remainder takes the divisor's side of
         * nought. What a reader that only has room for a signed 64-bit number asks is whether this
         * value fits, and not whether its magnitude does: the least such number is a divisor, and
         * its magnitude is one more than the greatest is.
         */
        public static BigInteger wholeDivisorOf(BigDecimal divisor) {
            ExactRatio ratio = ExactRatio.of(divisor);
            return ratio.isWhole() && ratio.floor() instanceof ExactAnswer.Held<BigInteger> held
                    && held.value().signum() != 0 ? held.value() : null;
        }

        /** The magnitude of {@link #wholeDivisorOf the divisor}, or null where there is none. */
        public static BigInteger magnitudeOf(BigDecimal divisor) {
            BigInteger whole = wholeDivisorOf(divisor);
            return whole == null ? null : whole.abs();
        }
    }

    /** A division of decimals rounded where the call says to round it. Not {@code /}, which answers
     *  the exact quotient and rounds nowhere. */
    record AQuotientRoundedToAScale() implements Arithmetic {

        @Override
        public List<Reads> reads() {
            return List.of(Reads.THE_NUMBER_IT_ANSWERS, Reads.THE_NUMBER_IT_ANSWERS,
                    Reads.A_SCALE, Reads.A_ROUNDING_MODE);
        }
    }

    /**
     * What one argument of a numeric operation is, as far as a fact about it needs to know.
     *
     * <p>What each of these <em>is</em>, said once. Which declaration answers to one, and whether
     * the library's signature agrees, is a question about the library and is asked where the
     * library is — {@code check.DischargeRules}, which holds every one of these facts to what the
     * library declares before a call is read. It used to be asked here, by comparing the argument's
     * type against a name written down beside it, which is a second answer to which type that is
     * (ADR-0087) and a backend's spelling in a package that is neutral about all of them (#1039).
     */
    enum Reads {

        /** A number of the kind the operation answers. */
        THE_NUMBER_IT_ANSWERS,

        /** How many places the answer is rounded to, which is a count and so an {@code Int}. */
        A_SCALE,

        /** Which way it rounds there. */
        A_ROUNDING_MODE
    }
}
