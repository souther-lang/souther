package souther.compiler.meaning;

import souther.compiler.check.NumericMeasures;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

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
