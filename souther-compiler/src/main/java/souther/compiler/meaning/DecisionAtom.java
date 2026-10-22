package souther.compiler.meaning;

import souther.compiler.check.NumericMeasures;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TraversalDirection;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * One quantity a comparison of a decision is written over.
 *
 * <p>Two sources and one arithmetic. What the input's numbers are is {@link NumericTerm}'s and is
 * taken as it is — the same terms a line is drawn on, so a column of the table and a border on the
 * same comparison cannot be about different quantities. What a dependency answered is this
 * reading's own, and it is held here rather than added to the input's vocabulary: what a search may
 * assume about the input and what a row may pin a dependency to are different licences, and a type
 * that carried both would hand each reader the other's.
 */
public sealed interface DecisionAtom extends Quantity {

    /** The answer of a dependency this is a number of, or null where it is a number of the input. */
    DecisionSubject.AnAnswer ofTheAnswer();

    /** {@code form}, every term of which is a number of the input, as a form over those numbers. */
    static LinearForm<DecisionAtom> ofTheInput(LinearForm<NumericTerm> form) {
        Map<DecisionAtom, ExactRatio> coefs = new LinkedHashMap<>();
        form.coefs().forEach((term, coefficient) -> coefs.put(new OfTheInput(term), coefficient));
        return new LinearForm<>(form.constant(), coefs);
    }

    /** A number of the behavior's input. */
    record OfTheInput(NumericTerm term) implements DecisionAtom {

        public OfTheInput {
            if (term == null) {
                throw new IllegalArgumentException("a number of the input is some term");
            }
        }

        @Override
        public DecisionSubject.AnAnswer ofTheAnswer() {
            return null;
        }

        @Override
        public String spelled() {
            return term.toString();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * A number {@code operation} takes of what a dependency answered, at the place inside its
     * answer the body read: how many it holds, how long it is, the hour it is at.
     *
     * <p>Which operations take a number of a value is what the library says of them, asked of the
     * same {@link NumericMeasures} the input's numbers are, so a count of a list is the count the
     * library defines wherever the list stands. What differs is whose value it is: one a row
     * stands a dependency in for, which no line of the input is drawn on.
     *
     * @param arguments what the call was given beside the value, as the library's account reads it
     * @param at        what stands at the place the number is taken of, which the account is
     *                  taken by
     */
    record TakenOfAnAnswer(ValueName.Stdlib operation, TakenArguments arguments,
                           DecisionSubject.AnAnswer of, Type at) implements DecisionAtom {

        public TakenOfAnAnswer {
            if (operation == null || arguments == null || of == null || at == null) {
                throw new IllegalArgumentException("a number taken of an answer is some"
                        + " operation's, of some answer");
            }
        }

        @Override
        public DecisionSubject.AnAnswer ofTheAnswer() {
            return of;
        }

        @Override
        public String spelled() {
            return operation + arguments.byPosition().toString() + "(" + of.spelled() + ")";
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * What {@code operation} adds up of a computation that turns on where each element of a list a
     * dependency answered stands: {@code List.sum(List.mapIndexed((i, x) -> i * x, answer))}.
     *
     * <p>Held as one number and not as a form of the elements' own numbers
     * ({@link Quantity.SumOver}), since the weight of an element is its position and no number the
     * element holds. The position counts from nought in the order {@code direction} hands the
     * answer's elements in — the order the answer lists them, or the opposite — so two such sums
     * over one list that part only in the direction are two numbers.
     *
     * @param list        the list the dependency answered
     * @param computation what the closure made of an element, which reads the position
     * @param each        what one computed value stands as
     */
    record ComputedOverAnAnswer(ValueName.Stdlib operation, DecisionSubject.AnAnswer list,
                                ElementValue computation, Type each,
                                TraversalDirection direction) implements DecisionAtom {

        public ComputedOverAnAnswer {
            if (operation == null || list == null || computation == null || each == null
                    || direction == null) {
                throw new IllegalArgumentException("a computed total of an answer is some"
                        + " operation's, of some list, handed in some direction");
            }
            if (!computation.readsThePosition()) {
                throw new IllegalArgumentException("{" + computation + "} turns on no element's"
                        + " position, and its total is one of the elements' own numbers");
            }
        }

        @Override
        public DecisionSubject.AnAnswer ofTheAnswer() {
            return list;
        }

        @Override
        public String spelled() {
            return operation + "{" + computation + " | " + list.spelled()
                    + (direction == TraversalDirection.REVERSE ? " from the far end" : "") + "}";
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /** A number a dependency answered with, at the place inside its answer the body read. */
    record OfAnAnswer(DecisionSubject.AnAnswer at) implements DecisionAtom {

        public OfAnAnswer {
            if (at == null) {
                throw new IllegalArgumentException("an answered number is some answer's");
            }
        }

        @Override
        public DecisionSubject.AnAnswer ofTheAnswer() {
            return at;
        }

        @Override
        public String spelled() {
            return at.spelled();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }
}
