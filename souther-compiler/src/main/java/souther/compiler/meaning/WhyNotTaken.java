package souther.compiler.meaning;

import souther.compiler.numeric.LinearForm;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * Why a reader of what a condition means did not take it into its own terms: what a row is asked
 * for, a column of a decision, what a path knows past a guard.
 *
 * <p>Three kinds, told apart by what it takes to lift one. The meaning was not read, which a rule
 * of the reading lifts; it was read and the domain the reader writes in has no words for it, which
 * widening the domain lifts; or it was read, the domain has the words, and the reader does not use
 * them yet, which a projection lifts. The last is never passed off as either of the others: what
 * this compiler has not written yet is not a fact about the model or the domain. None of them says
 * a row cannot be written, and one going away is a capability gained rather than a model changed.
 *
 * <p>One reason each, and a reader keeps every one it met. A condition made of parts can be
 * declined for one reason in one part and another in the next — one part's meaning unread, the
 * whole a shape the reader has no words for — and each is a different thing for somebody to do,
 * so none stands in for another.
 */
public sealed interface WhyNotTaken {

    /**
     * Why a relation over {@code form} was not taken by a reader of the input's own numbers: one
     * reason for each kind of quantity in it that is no number of the input, which the reader's
     * domain could carry and does not yet.
     */
    static List<WhyNotTaken> quantitiesNoRowWrites(LinearForm<Quantity> form) {
        Set<WhyNotTaken> out = new LinkedHashSet<>();
        for (Quantity atom : form.coefs().keySet()) {
            switch (atom) {
                case DecisionAtom.OfTheInput _ -> { }
                case DecisionAtom.OfAnAnswer _ ->
                        out.add(new ProjectionIncomplete(Shape.A_NUMBER_A_DEPENDENCY_ANSWERED));
                case Quantity.OfABinding _ ->
                        out.add(new ProjectionIncomplete(Shape.A_NUMBER_THE_BODY_BOUND));
                case Quantity.HowManyMeet _ ->
                        out.add(new ProjectionIncomplete(Shape.A_COUNT_OF_ELEMENTS));
            }
        }
        return List.copyOf(out);
    }

    /**
     * What the condition means was not read, for a reason the reading gives — carried as it gave
     * it. What it takes is a rule of the reading, and nothing a reader of it does.
     */
    record MeaningUnread(WhyUnread why) implements WhyNotTaken {

        public MeaningUnread {
            Objects.requireNonNull(why, "an unread meaning is unread for some reason");
        }
    }

    /**
     * What the condition means was read, and the domain the reader writes in cannot say it, which
     * takes widening that domain.
     */
    record OutsideDomain(DomainLimit limit) implements WhyNotTaken {

        public OutsideDomain {
            Objects.requireNonNull(limit, "a domain stops somewhere");
        }
    }

    /**
     * What the condition means was read, and the reader's domain could say it, and the reader does
     * not yet. About this compiler and not about the model or the domain: what it takes is a
     * projection written for {@code shape}.
     */
    record ProjectionIncomplete(Shape shape) implements WhyNotTaken {

        public ProjectionIncomplete {
            Objects.requireNonNull(shape, "a projection falls short of some shape");
        }
    }

    /** Where a reader's domain has no words for what a condition means. */
    enum DomainLimit {

        /**
         * A quantity read from end to end that stands on no order a region measures values on:
         * {@code a == b} over two records is read perfectly, and what it comes to is a difference
         * between two positions that is a distance on nothing. What is here for an author to act
         * on is the carrier — a position whose values this compiler measures on nothing is one
         * every rule about it is unrepresented in.
         */
        A_QUANTITY_ON_NO_ORDER,

        /**
         * What a container's elements are asked for comes to how many it holds, and no type
         * measures that container's size: some element meeting what every element meets is the
         * container holding one, and every element meeting what none meets is it holding none.
         */
        A_SIZE_NOTHING_MEASURES,

        /**
         * One of several things, or some element meeting something, as what a path knows: a path
         * knows a set of facts that all hold, and which of several holds, or which element, is no
         * fact of it.
         */
        A_PATH_KNOWS_NO_ALTERNATIVES
    }

    /** A shape of what a condition means that a reader's domain could state and the reader does
     *  not state yet. */
    enum Shape {

        /**
         * One of several things: a disjunction, a conjunction coming out false, or one statement
         * on each application of a closure. Taking any one of them would exclude rows that arrive
         * through another.
         */
        ONE_OF_SEVERAL_THINGS,

        /**
         * Every element of a container meeting something that says more than the element. Every
         * element meeting it is also what an empty container does, whatever the rest says, so a
         * row past it need not meet that part.
         */
        EVERY_ELEMENT_AND_MORE,

        /** A quantifier inside a quantifier: what an element's own elements meet. */
        A_QUANTIFIER_WITHIN_ONE,

        /** A truth of an element, which nothing composing a container's elements writes. */
        A_TRUTH_OF_AN_ELEMENT,

        /** A truth, a value being there or a case of what a dependency answered, which a row
         *  stands in and nothing composes against yet. */
        WHAT_A_DEPENDENCY_ANSWERED,

        /** Which case a subject is, outside an arm of a fork. */
        THE_CASE_OF_A_SUBJECT,

        /** An optional of the input holding a value. */
        A_VALUE_BEING_THERE,

        /** Two subjects being one value, outside what an element of a container is. */
        TWO_SUBJECTS_ONE_VALUE,

        /** A relation over a number a dependency answered. */
        A_NUMBER_A_DEPENDENCY_ANSWERED,

        /** A relation over a number of a value the body bound, which the reading named by its
         *  binding rather than reading it through. */
        A_NUMBER_THE_BODY_BOUND,

        /** A relation over how many elements of a container meet something. */
        A_COUNT_OF_ELEMENTS,

        /** A place on an order, of a term that is no one position. */
        AN_ORDER_OF_NO_ONE_POSITION,

        /** Several demands that one column of a decision would have to be. */
        SEVERAL_DEMANDS_IN_ONE_COLUMN,

        /** Some or every element meeting something, as a column of a decision: which element did
         *  is nothing a value at one position says. */
        A_QUANTIFIER_AS_A_COLUMN,

        /**
         * An arm of a fork read off the pattern and the scrutinee as written, which comes to no
         * narrowing of a position: a pattern selecting no cases, or a scrutinee standing at none.
         */
        AN_ARM_READ_AS_WRITTEN,

        /** An arm of an attempt, which the invariant a construction checks decides. */
        AN_ARM_AN_INVARIANT_DECIDES,

        /** A truth of the input, asked of what the rules leave that position: which of its two
         *  values the rules let stand. */
        A_TRUTH_ASKED_OF_THE_RULES,

        /** Some or every element of a container meeting something, asked of what the rules leave
         *  the container and its elements. */
        SOME_ELEMENT_ASKED_OF_THE_RULES,

        /** A number or a truth of the input at a position the tree a path is walked over holds
         *  no place for. */
        A_POSITION_THE_PATH_HAS_NO_PLACE_FOR,

        /** A place on an order, as a fact of a path. */
        A_PLACE_ON_AN_ORDER
    }
}
