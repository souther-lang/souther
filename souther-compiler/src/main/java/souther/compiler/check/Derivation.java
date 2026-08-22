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

    /**
     * The forms this recipe is read from.
     *
     * <p>Answered by the recipe and not worked out from its shape. What a recipe is read from is not
     * the same question as what it is arithmetic over, and the two look alike only while every
     * recipe is arithmetic: a product's operands are both, and a choice's arms are read from without
     * being arithmetic over anything, and what chose between them would be read from without even
     * standing in the answer. A reader that decided the question by looking at which components
     * happen to be forms would be answering a semantic question by a naming convention, and would
     * miss the first one that arrives inside something else.
     *
     * <p>What it is for is {@link Terms#reached}, which is what says which places a form is about.
     * {@link StepInputFacts} keeps only the places a step names, so a form a recipe is read from and
     * that walk does not reach leaves those places unbounded — and nothing else says so.
     *
     * <p>Abstract, so that a recipe added later is asked this before it compiles.
     */
    List<LinearForm<FactSubject>> formsRead();

    record Product(LinearForm<FactSubject> left, LinearForm<FactSubject> right) implements Derivation {

        @Override
        public List<LinearForm<FactSubject>> formsRead() {
            return List.of(left, right);
        }
    }

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
     * <p>What is recorded is the arms, and what choosing one settles is not here yet. What settles
     * it holds exactly where that arm is the answer, so an arm read under it says more than the arm
     * alone: {@code if a + x < 100 then a + x else 100} lies below a hundred only by its condition,
     * and a {@code match} arm's body reading what the arm bound reads a value only that arm has.
     * Reading either needs the account of what an arm settles that {@link PathEngine} keeps, which
     * is a thing to have once and not twice. Until that account is somewhere both readers can ask,
     * the range is the arms together — sound, and wider than the value's own range, so the fragment
     * this recognises is narrower than what a source can express (#973).
     *
     * <p>The operations the library defines by cases ({@code DischargeRules.CHOOSES}) are choices
     * with no producer here yet (#974). Which values a choice is one of does have an owner
     * ({@link Choice}), so a kind of choice is found by every reader at once or by none.
     *
     * <p>All of that is this recipe unfinished and not this recipe's limit. What a choice is — a
     * value that is one of several — is what is settled here; how finely each arm is read, and which
     * operations produce one, are the parts still to connect.
     *
     * @param arms what stands in each arm, as a form each. Every arm or none: an arm the walk could
     *             not read leaves the choice with no recipe at all, since a range that left one of
     *             them out would be a range the value can be outside of. Never none of them — one of
     *             several is what this is, so a producer handing over an empty list has disagreed
     *             with that rather than described a value, and a reader taking it for a range with
     *             no ends would hide the disagreement as a loss of precision.
     */
    record Chosen(List<LinearForm<FactSubject>> arms) implements Derivation {

        public Chosen {
            arms = List.copyOf(arms);
            if (arms.isEmpty()) {
                throw new IllegalArgumentException("a value that is one of several was recorded with"
                        + " none to be one of");
            }
        }

        @Override
        public List<LinearForm<FactSubject>> formsRead() {
            return arms;
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
                    NumericDomain.Bounds divisorExtent) implements Derivation {

        /** The extent is not among them: it is what the operator's divisor can be at all, which is a
         * range and names no place. */
        @Override
        public List<LinearForm<FactSubject>> formsRead() {
            return List.of(numerator, divisor);
        }
    }
}
