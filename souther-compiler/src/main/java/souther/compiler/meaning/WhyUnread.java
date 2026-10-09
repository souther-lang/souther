package souther.compiler.meaning;

import souther.compiler.check.Clause;
import souther.compiler.check.ClausesInOrder;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.Unsayable;
import souther.compiler.types.ValueName;

import java.util.Objects;

/**
 * Why part of a condition was read as nothing.
 *
 * <p>Kept apart by what they are owed. Most say what the domain the reading is over has no words for
 * at the place it stopped, and nothing written in this reading would read the part. Two say the
 * opposite, each of what this compiler holds itself to and not of the model: that what is stated
 * of a library operation is not proved against its body yet ({@link NotProvedOfItsBody}), which is
 * lifted by a proof; and that the part could be read and this compiler declined the work at a figure
 * it holds itself to ({@link MoreReadingsThanAreMade}), which is lifted by raising the figure. Where
 * a part follows from what the language and the library already say, the reading takes it: no part
 * is left for a step this reading does not take.
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
     * An operation the library declares no law of, for how its answer comes out on {@code aspect}:
     * one whose declaration does not give its answer that side, such as a walk answering whatever
     * its step does. Every operation whose declared answer has the side is settled, by a law or by
     * {@link NoWordsFor}.
     */
    record NoLawFor(ValueName.Stdlib operation, AnswerAspect aspect) implements WhyUnread {

        public NoLawFor {
            Objects.requireNonNull(operation, "a law is of an operation");
            Objects.requireNonNull(aspect, "a law is about one side of what it answers");
        }
    }

    /**
     * How {@code operation}'s answer comes out on {@code aspect} comes to {@code proposition}, which
     * the domain has no words for: what it states is known, and no proposition over the input says
     * it.
     */
    record NoWordsFor(ValueName.Stdlib operation, AnswerAspect aspect, Unsayable proposition)
            implements WhyUnread {

        public NoWordsFor {
            Objects.requireNonNull(operation, "a closing is of an operation");
            Objects.requireNonNull(aspect, "about one side of what it answers");
            Objects.requireNonNull(proposition, "and names what that comes to");
        }
    }

    /**
     * What is stated of how {@code operation}'s answer comes out on {@code aspect} is not proved
     * against the operation's body, so it is an obligation still open and no law: about what this
     * compiler has shown, and neither about the domain's words nor about an operation nothing is
     * stated of.
     */
    record NotProvedOfItsBody(ValueName.Stdlib operation, AnswerAspect aspect)
            implements WhyUnread {

        public NotProvedOfItsBody {
            Objects.requireNonNull(operation, "a statement is of an operation");
            Objects.requireNonNull(aspect, "about one side of what it answers");
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
     * A clause of the invariant an attempt checks, which could not be read where the attempt
     * builds its value: whether it holds there is what decides between the attempt's arms.
     */
    record AClauseOfAnInvariant(Clause.Ref clause, ClausesInOrder.WhyAClauseIsUnread why)
            implements WhyUnread {

        public AClauseOfAnInvariant {
            Objects.requireNonNull(clause, "a clause left unread is some clause");
            Objects.requireNonNull(why, "a clause is left unread for some reason");
        }
    }

    /**
     * The invariant an attempt checks, where a declaration whose clauses govern the value built
     * could not be reached: which clauses there are, and so which of them fails first, is not
     * known.
     */
    record AnInvariantNotReached() implements WhyUnread {}

    /**
     * What a behavior called by name answers turns, in its body read where the call stands, on
     * something a call is not the place to say anything about.
     */
    record InACalledBody(What what) implements WhyUnread {

        public InACalledBody {
            Objects.requireNonNull(what, "the body turns on something");
        }

        /** What the called body's answer turns on, that the call cannot say. */
        public enum What {

            /**
             * What one of its own dependencies answers. A row stands in the caller's dependencies
             * and not the called behavior's, and which answer it is was named by an evaluation in
             * that body, which each call makes afresh.
             */
            WHAT_ITS_DEPENDENCY_ANSWERS,

            /** The behavior itself, reached again while its own answer is being read. */
            ITSELF,

            /** Nothing: the body of the behavior was not read, or it is called with some other
             *  number of values than it takes. */
            AN_ANSWER_NOT_READ
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
     * A construct met in several copies — a helper's, wherever the helper is written — whose copies
     * state different things, so the construct states none of them.
     */
    record CopiesStateDifferentThings() implements WhyUnread {}

    /** A construct the reading of what a body's conditions mean did not meet. */
    record NotMetByTheReading() implements WhyUnread {}
}
