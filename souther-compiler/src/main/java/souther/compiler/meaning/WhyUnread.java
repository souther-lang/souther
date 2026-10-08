package souther.compiler.meaning;

import souther.compiler.semantics.AnswerAspect;
import souther.compiler.types.ValueName;

import java.util.Objects;

/**
 * Why part of a condition was read as nothing.
 *
 * <p>Two kinds, kept apart because they are owed different things. Most say what the domain the
 * reading is over has no words for at the place it stopped, and nothing written in this reading
 * would read the part. {@link NotYetComposed} says the opposite: the part follows from what the
 * language and the library already say, and the step that would take it is not written. That one
 * is an obligation of this compiler's and not a fact about the model, and naming the step is what
 * lets it be counted and closed.
 *
 * <p>Only the reading of what a condition means says one of these. That a reader of the proposition
 * has no demand for a part it was handed is that reader's to say in its own words, and putting it
 * here would turn a part that was read into one that was not. Sealed, so a reason added is one
 * every reader that says it in its own words has to say.
 */
public sealed interface WhyUnread {

    /** What a part of a condition is about stands at no position of the input. */
    record AtNoPosition(Place what) implements WhyUnread {

        public AtNoPosition {
            Objects.requireNonNull(what, "something stood at no position");
        }

        /** Which thing a condition is about stood nowhere a row writes. */
        public enum Place {

            /** The container a condition asks what it holds, or one of whose elements it reads. */
            CONTAINER,

            /** The value a condition asks whether a container holds. */
            VALUE,

            /** The value a {@code match} chooses its arm by. */
            SCRUTINEE,

            /**
             * The value whose truth, holding anything or holding a value a condition asks, where
             * nothing it is made by is followed back to the input.
             */
            SUBJECT
        }
    }

    /**
     * What a condition asks of a container comes to how many it holds, and its type has no size this
     * input measures.
     */
    record NoMeasureOfItsSize() implements WhyUnread {}

    /** A comparison whose relation is no form over the quantities a condition is read over. */
    record OutsideTheLinearFragment() implements WhyUnread {}

    /**
     * A container quantified inside a quantifier over itself: the element is what stands at the
     * container's element, so two elements of one container would be one subject.
     */
    record TwoElementsOfOneContainer() implements WhyUnread {}

    /**
     * An operation the library declares no law of, for how its answer comes out on {@code aspect}.
     */
    record NoLawFor(ValueName.Stdlib operation, AnswerAspect aspect) implements WhyUnread {

        public NoLawFor {
            Objects.requireNonNull(operation, "a law is of an operation");
            Objects.requireNonNull(aspect, "a law is about one side of what it answers");
        }
    }

    /**
     * What a helper answers where the helper calls itself, so its body is not one expression to read
     * through.
     */
    record WhatARecursiveHelperAnswers() implements WhyUnread {}

    /**
     * A part that follows from what the language and the library already say, through a step this
     * reading does not take yet.
     */
    record NotYetComposed(Step step) implements WhyUnread {

        public NotYetComposed {
            Objects.requireNonNull(step, "an obligation names the step it is owed");
        }

        /**
         * The steps owed. One goes when the rule that takes it is written, so the set says what is
         * left to write and nothing else.
         */
        public enum Step {

            /**
             * A comparison over values the body bound, read as the arithmetic the language composes
             * them by: through a binding, a sum, a scaled value, a number written out, a newtype,
             * and beside a position of the input.
             */
            A_FORM_OVER_BOUND_VALUES,

            /**
             * A number an operation answers whose sign the library says states which of its
             * arguments is the greater, compared where its arguments are values the body bound.
             */
            AN_ORDER_OF_ITS_ARGUMENTS,

            /** A number an operation answers by choosing among cases of its arguments. */
            A_CHOICE_BY_CASES,

            /**
             * A comparison over one of several values the source wrote out, each of which the name
             * stands for on some application.
             */
            VALUES_WRITTEN_OUT,

            /** The truth of what a dependency of the behavior answers. */
            A_DEPENDENCYS_ANSWER,

            /** A closure handed to an operation as a name rather than written where it is handed. */
            A_CLOSURE_BY_NAME
        }
    }
}
