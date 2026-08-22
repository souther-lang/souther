package souther.compiler.check;

import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.LinearForm;

import java.util.List;

/**
 * How a value the affine fragment cannot carry was computed from values it can.
 *
 * <p>What is recorded here is the construction's own meaning and nothing the path says. The same
 * expression is read more than once — under what the guards established, and under what holds of the
 * values whatever the guards did — and a fact that depends on which reading is asking belongs to the
 * reading and not to this. So a recipe states what was computed and what the operator is, and
 * everything about where the operands lie is applied where the recipe is read
 * ({@link DerivedNumericFacts}).
 *
 * <p>That is not a rule against choosing here. Which operators have a recipe at all is a question
 * about the operator and not about the path — {@code /} on {@code Decimal} rounds at a precision the
 * run time sets and has none for that reason — and choices of that kind are made where the recipe is
 * recorded ({@link Terms}).
 */
sealed interface Derivation {

    /**
     * The forms this was computed from, in the order the operation takes them.
     *
     * <p>Here so that a reader asking what a recipe is built out of asks the recipe. Which values a
     * recipe reaches, and whether two readings computed a value the same way, are questions about
     * every recipe there is — answered by switching on the kind, each is a place a recipe added
     * later is silently left out of, and one of them going quiet is a fact never derived rather than
     * a compile error.
     */
    List<LinearForm<FactSubject>> operands();

    /** Every value the operator's divisor can take, or null where the recipe divides by nothing. */
    NumericDomain.Bounds divisorExtent();

    record Product(LinearForm<FactSubject> left, LinearForm<FactSubject> right) implements Derivation {

        @Override
        public List<LinearForm<FactSubject>> operands() {
            return List.of(left, right);
        }

        @Override
        public NumericDomain.Bounds divisorExtent() {
            return null;
        }
    }

    /**
     * A truncating divide.
     *
     * @param numerator     what is divided.
     * @param divisor       what it is divided by. A form and not a written number: a divisor the
     *                      path bounds away from zero has the sign and the magnitude the rule needs
     *                      as surely as a written one does, and holding it as a number was what left
     *                      every divisor with a coefficient unread.
     * @param divisorExtent every value the operator's divisor can take, which is what its type
     *                      holds. Not a bound the path proves — the arithmetic composed over a form
     *                      runs over numbers of any size, and the operator's divisor is a value of
     *                      its own type, so a range with none of them in it is not a divisor this
     *                      operator has. Read where the recipe is read, and not a fact about any
     *                      path.
     */
    record TruncatingQuotient(LinearForm<FactSubject> numerator, LinearForm<FactSubject> divisor,
                              NumericDomain.Bounds divisorExtent) implements Derivation {

        @Override
        public List<LinearForm<FactSubject>> operands() {
            return List.of(numerator, divisor);
        }
    }

    /**
     * What that divide leaves of what it divided.
     *
     * <p>The same three parts and for the same reasons, because it is the same division: what is
     * known of a remainder is decided by the sign of what was divided and by how big the divisor is,
     * and both are read where the recipe is read. Held as its own recipe and not as the arithmetic
     * {@code numerator - divisor * quotient} it satisfies: that identity is a fact about the two
     * answers of one division and not a way of computing either, and writing it as one would make
     * what a remainder is depend on {@code /} answering at all — which for one pair of {@code Int}s
     * it does not (spec §stdlib-int).
     */
    record TruncatingRemainder(LinearForm<FactSubject> numerator, LinearForm<FactSubject> divisor,
                               NumericDomain.Bounds divisorExtent) implements Derivation {

        @Override
        public List<LinearForm<FactSubject>> operands() {
            return List.of(numerator, divisor);
        }
    }
}
