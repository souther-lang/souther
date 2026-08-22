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
 * ({@link DerivedBounds}).
 *
 * <p>That is not a rule against choosing here. Which operators have a recipe at all is a question
 * about the operator and not about the path — {@code /} on {@code Decimal} rounds at a precision the
 * run time sets and has none for that reason — and choices of that kind are made where the recipe is
 * recorded ({@link Terms}).
 */
sealed interface Derivation {

    record Product(LinearForm<FactSubject> left, LinearForm<FactSubject> right) implements Derivation {}

    /**
     * A value that is one of several: an {@code if}, a {@code match}, and anything else that answers
     * one of the values standing in it.
     *
     * <p>Not arithmetic, and here beside the arithmetic for the reason this interface gives: what is
     * recorded is how a value was computed, and being one of several is a way of computing one. The
     * affine walk already names such a node — a choice is one value, and a rule written about it is
     * about the thing that stands there — and until this arm existed nothing was filed under that
     * name, so the value came out with no range whatever its arms answered.
     *
     * <p>What is recorded is the arms and not what chose between them. The condition holds exactly
     * where its arm is the answer, so reading it would sharpen this — {@code if a + x < 100 then
     * a + x else 100} lies below a hundred only by its conditions — and it is a second reading of
     * conditions beside {@link Predicates#assumeCond}, which is a thing to do once and not twice.
     * Left out, the range is the arms together, which is sound and is narrower than what an author
     * can write.
     *
     * @param arms what stands in each arm, as a form each. Every arm or none: an arm the walk could
     *             not read leaves the choice with no recipe at all, since a range that left one of
     *             them out would be a range the value can be outside of.
     */
    record Chosen(List<LinearForm<FactSubject>> arms) implements Derivation {

        public Chosen {
            arms = List.copyOf(arms);
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
    record Quotient(LinearForm<FactSubject> numerator, LinearForm<FactSubject> divisor,
                    NumericDomain.Bounds divisorExtent) implements Derivation {}
}
