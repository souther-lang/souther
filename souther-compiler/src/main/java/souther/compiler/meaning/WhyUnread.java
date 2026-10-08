package souther.compiler.meaning;

import souther.compiler.numeric.UnheldNumber;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.types.ValueName;

import java.util.Objects;

/**
 * Why part of a condition was read as nothing.
 *
 * <p>Three kinds, kept apart because they are owed different things. Most say what the domain the
 * reading is over has no words for at the place it stopped, and nothing written in this reading
 * would read the part. {@link NotYetComposed} says the opposite: the part follows from what the
 * language and the library already say, and the step that would take it is not written. That one
 * is an obligation of this compiler's and not a fact about the model, and naming the step is what
 * lets it be counted and closed. And one says neither: that the part could be read and this compiler
 * declined the work at a figure it holds itself to ({@link MoreReadingsThanAreMade}), which is
 * lifted by raising the figure and by nothing written in the model.
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

    /**
     * A comparison over arithmetic no form over the quantities a condition is read over says: a
     * product of two of them, a quotient by one.
     */
    record OutsideTheLinearFragment() implements WhyUnread {}

    /**
     * A comparison whose form over those quantities was worked out exactly, with a number in it that
     * could not be held: the relation is linear, and what it is cannot be written down here.
     */
    record ANumberNotHeld(UnheldNumber why) implements WhyUnread {

        public ANumberNotHeld {
            Objects.requireNonNull(why, "a number not held is not held for a reason");
        }
    }

    /**
     * A comparison over arithmetic no run has a number for — a quotient by nought, the least whole
     * number negated: the run aborts there, so there is no relation for the comparison to state.
     */
    record NoNumberOnARun() implements WhyUnread {}

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

    /** A number an operation answers, of which the library states no form over its arguments. */
    record NoFormOfWhatItAnswers(ValueName.Stdlib operation) implements WhyUnread {

        public NoFormOfWhatItAnswers {
            Objects.requireNonNull(operation, "a number is answered by an operation");
        }
    }

    /**
     * A number {@code measure} takes of what {@code madeBy} answers, which stands at no position and
     * of which the library says nothing in terms of what {@code madeBy} was handed.
     */
    record ANumberOfWhatAnOperationAnswers(ValueName.Stdlib measure, ValueName.Stdlib madeBy)
            implements WhyUnread {

        public ANumberOfWhatAnOperationAnswers {
            Objects.requireNonNull(measure, "a number is taken by an operation");
            Objects.requireNonNull(madeBy, "of what an operation answered");
        }
    }

    /**
     * What a helper answers where the helper calls itself, so its body is not one expression to read
     * through.
     */
    record WhatARecursiveHelperAnswers() implements WhyUnread {}

    /**
     * A part that would be read once for each application of the closures it is in, or each case
     * of what it compares, more times than the reading of what a condition means makes. A figure
     * of this compiler's work was reached, and nothing is said of the model.
     */
    record MoreReadingsThanAreMade() implements WhyUnread {}

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
             * The size of what an operation answers where the library says it answers as many as it
             * was handed, read as the size of what it was handed.
             */
            A_SIZE_AN_OPERATION_KEEPS,

            /**
             * A value chosen by cases where the choice is not a side of a comparison of numbers:
             * inside arithmetic, where what each case answers has to be carried out through what is
             * computed from it, or compared as a value no carrier counts — two truths neither
             * written out, two strings.
             */
            A_CHOICE_BY_CASES,

            /**
             * A comparison over one of several values the source wrote out, each of which the name
             * stands for on some application, where which value an application hands cannot be said
             * where the condition is read: one naming a binding of the place it was written, and
             * standing at no position.
             */
            VALUES_WRITTEN_OUT,

            /**
             * What a dependency answers when asked about a value the model computes from what a row
             * controls. A row asks it the same thing however it is spelled, so the answer is one the
             * row stands in; naming it takes naming the value it was asked about, which only a
             * subject or a number written out is named by so far.
             */
            A_DEPENDENCY_ASKED_ABOUT_A_COMPUTED_VALUE,

            /** What a behavior called by name answers, which its body computes. */
            A_BEHAVIOR_CALLED_BY_NAME,

            /** A closure handed to an operation as a name rather than written where it is handed. */
            A_CLOSURE_BY_NAME
        }
    }
}
