package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BinOp;

/**
 * What a value the check reads as a number was computed. Not how it was written, and not what
 * follows from it.
 *
 * <p>The one answer to "which arithmetic is this". A division reaches the check through more than
 * one surface — the operator, the library's function form, the value case of a function that answers
 * a zero divisor as a case — and what decides the rules about it is that it is a truncating
 * quotient of two operands, which every surface has and none of them owns. Read once here, so that
 * a term, an atom and a recipe are all built off one reading; asked of the shape of the node
 * instead, each surface is a second entry in a table and the next surface is a third (#959).
 *
 * <p>Operands are {@link Core}, never a form. What arithmetic a value comes to is
 * {@link AffineForms}' to say and one walk says it (ADR-0111); a meaning that carried forms would be
 * a second account of the arithmetic, kept beside the walk that has one and weaker than it by
 * exactly the values it cannot read.
 *
 * <p>What this states is the operation's own semantics and nothing a path says, as
 * {@link Derivation} does — the two are apart because they answer different questions. This says
 * what was computed. {@link Derivation} says what of that the numeric fragment can prove in, which
 * is less: {@code Decimal.divide} has a meaning here and a recipe only where its scale is a number
 * the reading holds, and the value case of {@code Int.divide} had a meaning here before anything
 * derived a bound from it.
 */
sealed interface NumericMeaning {

    /**
     * Arithmetic the language writes as an operator, over two operands in the order written.
     *
     * <p>{@code /} over {@code Decimal} is here and is not a quotient below: it rounds to a
     * significant-digit precision the run time sets rather than to a scale the domain chose
     * (spec §stdlib-decimal), which is a different operation from the one
     * {@link RoundedQuotient} states. Nothing derives a range from it, as nothing did before.
     */
    record Operator(BinOp op, Core left, Core right) implements NumericMeaning {

        /**
         * Which operators this is about, said where one arrives rather than left to the readings
         * that meet it.
         *
         * <p>An operator answering something else is not arithmetic the language wrote, and a
         * reader of this holds one that is: everything below takes the operator as naming a number
         * two operands come to, and a comparison arriving here would be named as though it were
         * one.
         */
        public Operator {
            if (!op.answersANumber()) {
                throw new IllegalArgumentException(
                        "arithmetic is what this is about, and this answers no number: " + op);
            }
        }
    }

    /** A division of whole numbers, truncated toward zero (spec §stdlib-int). */
    record TruncatingQuotient(Core dividend, Core divisor) implements NumericMeaning {}

    /** What is left of the dividend by that division, which takes the dividend's sign. */
    record TruncatingRemainder(Core dividend, Core divisor) implements NumericMeaning {}

    /**
     * A division of decimals rounded to a scale and a mode the call states
     * (spec §stdlib-decimal).
     *
     * @param scale how many places the answer is rounded to. The expression, not a number: whether
     *              it reads as one is a question about a reading, and this is not one
     * @param mode  which way it rounds there. Kept because it is part of which value this is, and
     *              read by nothing that bounds it — every mode leaves the answer between the same
     *              two points of the scale's grid
     */
    record RoundedQuotient(Core dividend, Core divisor, Core scale, Core mode)
            implements NumericMeaning {}
}
