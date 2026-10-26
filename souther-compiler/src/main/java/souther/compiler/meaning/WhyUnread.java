package souther.compiler.meaning;

import souther.compiler.check.Clause;
import souther.compiler.check.ClausesInOrder;
import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.check.NonAffineOperation;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.observe.Figure;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.Unsayable;
import souther.compiler.types.ValueName;

import java.util.Objects;
import java.util.Optional;

/**
 * Why part of a condition was read as nothing.
 *
 * <p>Kept apart by what they are owed. Most say what the domain the reading is over has no words for
 * at the place it stopped, and nothing written in this reading would read the part. Three say the
 * opposite, each of what this compiler holds itself to and not of the model: that what is stated
 * of a library operation is not proved against its body yet ({@link NotProvedOfItsBody}), which is
 * lifted by a proof; and that the part could be read and this compiler declined the work at a figure
 * it holds itself to — how many readings of a condition are made
 * ({@link MoreReadingsThanAreMade}), or how far a container is written out
 * ({@link MoreElementsThanAreWrittenOut}) — which is lifted by raising that figure. Where
 * a part follows from what the language and the library already say, the reading takes it: no part
 * is left for a step this reading does not take.
 *
 * <p>Only the reading of what a condition means says one of these. That a reader of the proposition
 * has no demand for a part it was handed is that reader's to say in its own words, and putting it
 * here would turn a part that was read into one that was not. Sealed, so a reason added is one
 * every reader that says it in its own words has to say.
 */
public sealed interface WhyUnread {

    /** A part read more times than the reading of one condition makes along one way down. */
    WhyUnread PAST_THE_READINGS = new MoreReadingsThanAreMade();

    /** A part read once more where the reading had made as many readings in all as it makes. */
    WhyUnread PAST_THE_TOTAL_READINGS = new MoreTotalReadingsThanAreMade();

    /** A part whose step states more parts, written out, than a step is concluded with. */
    WhyUnread PAST_THE_PARTS = new MorePartsThanAreConcluded();

    /** A part whose statement is over more ways of keeping than are written out to find what it
     *  comes to. */
    WhyUnread PAST_THE_WAYS = new MoreWaysThanAreWrittenOut();

    /** A part about a container holding more than a walk writes out. */
    WhyUnread PAST_THE_ELEMENTS = new MoreElementsThanAreWrittenOut();

    /**
     * The figure of this compiler's work the part stopped at, or none where it stopped at none.
     *
     * <p>A reason that stops at a figure holds nothing beside it, since the figure is fixed where it
     * is declared, so each is one value, made above: a reader's word for one holds that value as
     * what it says, and makes no reason of its own.
     *
     * <p>The one place that says which. A reader that says a part stopped at a figure — what a
     * report owes, what a wider run may read past, which budget a composer names — asks this, so a
     * reason that stops at a figure is one every such reader says the figure of. Each reader
     * telling the reasons apart for itself, a reason added was one of them said as a part no
     * further reading would read.
     */
    default Optional<Figure> figure() {
        return switch (this) {
            case MoreReadingsThanAreMade _ ->
                    Optional.of(CompositionBudget.READINGS_OF_ONE_CONDITION.figure());
            case MoreTotalReadingsThanAreMade _ ->
                    Optional.of(CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION.figure());
            case MorePartsThanAreConcluded _ ->
                    Optional.of(CompositionBudget.PARTS_A_DERIVATION_CONCLUDES.figure());
            case MoreWaysThanAreWrittenOut _ ->
                    Optional.of(CompositionBudget.WAYS_A_STATEMENT_IS_WRITTEN_OUT_OVER.figure());
            case MoreElementsThanAreWrittenOut _ -> Optional.of(
                    WorkFigure.ELEMENTS_A_WALK_WRITES_OUT.at(ElementsWrittenOut.MOST_WALKED));
            case AtNoPosition _, NoMeasureOfItsSize _, OutsideTheLinearFragment _,
                 NotArithmetic _, ANumberNotHeld _, NoNumberOnARun _,
                 TwoElementsOfOneContainer _, NoLawFor _, NoWordsFor _, NotProvedOfItsBody _,
                 NoFormOfWhatItAnswers _, ANumberOfWhatAnOperationAnswers _,
                 CodePointsOfWhatAnOperationAnswers _, AClauseOfAnInvariant _, AnInvariantNotReached _, InACalledBody _,
                 WhatARecursiveHelperAnswers _, SeveralValuesNotGoneInto _,
                 CopiesStateDifferentThings _, NotMetByTheReading _,
                 WhichElementARunStopsAt _ -> Optional.empty();
        };
    }

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

            /** A string a condition asks whether it stands inside another, or whether another
             *  stands inside it. */
            STRING,

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
     *
     * @param operation which of those it was, as the arithmetic that met it decided
     */
    record OutsideTheLinearFragment(NonAffineOperation operation) implements WhyUnread {}

    /**
     * A part of a comparison that is no arithmetic a form could say: an operator that answers no
     * number, or a condition that holds or fails whatever the element is.
     *
     * <p>Its own case beside {@link OutsideTheLinearFragment}, which is arithmetic with a shape no
     * form has. Nothing is multiplied or divided here, so a reader told of a product would look for
     * one that is not written.
     */
    record NotArithmetic() implements WhyUnread {}

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
     * What {@code observed} of {@code operation}'s answer — a side of it, or how many it holds —
     * comes to is {@code proposition}, which the domain has no words for: what it states is known,
     * and no proposition over the input says it.
     */
    record NoWordsFor(ValueName.Stdlib operation, OperationLaw.Observed observed,
                      Unsayable proposition) implements WhyUnread {

        public NoWordsFor {
            Objects.requireNonNull(operation, "a closing is of an operation");
            Objects.requireNonNull(observed, "about something observed of what it answers");
            Objects.requireNonNull(proposition, "and names what that comes to");
        }
    }

    /**
     * What is stated of what {@code observed} of {@code operation}'s answer comes to is not proved
     * against the operation's body, so it is an obligation still open and no law: about what this
     * compiler has shown, and neither about the domain's words nor about an operation nothing is
     * stated of.
     */
    record NotProvedOfItsBody(ValueName.Stdlib operation, OperationLaw.Observed observed)
            implements WhyUnread {

        public NotProvedOfItsBody {
            Objects.requireNonNull(operation, "a statement is of an operation");
            Objects.requireNonNull(observed, "about something observed of what it answers");
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
     * How many of the code points of what {@code madeBy} answers are in a class, where that string
     * stands at no position: no law of {@code madeBy} says that count in terms of what it was
     * handed.
     */
    record CodePointsOfWhatAnOperationAnswers(ValueName.Stdlib madeBy) implements WhyUnread {

        public CodePointsOfWhatAnOperationAnswers {
            Objects.requireNonNull(madeBy, "the string was answered by an operation");
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
     *
     * <p>Said only where the readings were counted against that figure and came out past it. A
     * value the reading has to go into is not past it for being one: whether going in is past it
     * is the count's answer, made where the reading goes in.
     */
    record MoreReadingsThanAreMade() implements WhyUnread {}

    /**
     * A part that would be read once more where the reading of what its condition means had made
     * as many readings in all as it makes — every case, value and application of every way down
     * counted together, where {@link MoreReadingsThanAreMade} counts one way down. A figure of
     * this compiler's work was reached, and nothing is said of the model.
     *
     * <p>Its own reason and not that one, because the two are two figures: a reader told the
     * wrong one would raise a figure that stopped nothing.
     */
    record MoreTotalReadingsThanAreMade() implements WhyUnread {}

    /**
     * A step of the reading whose statement, written out with every part it holds as many times as
     * it holds it, comes to more parts than a step is concluded with. A figure of this compiler's
     * work was reached, and nothing is said of the model.
     *
     * <p>Not a count of readings: one reading can be stated more than once — a condition is stated
     * where it holds and denied where it does not, and an arm of a match is stated beside the
     * denial of every arm before it — so a statement grows with how deep such steps stand inside
     * one another, however few readings it was made of.
     */
    record MorePartsThanAreConcluded() implements WhyUnread {}

    /**
     * A step of the reading whose statement is over more ways of keeping the elements of a
     * container than are written out to find what it comes to. A figure of this compiler's work
     * was reached, and nothing is said of the model.
     *
     * <p>Not {@link MorePartsThanAreConcluded}: that one says what the statement came to, and
     * this says it was not written out to be counted. Ways that all state alike come to a few
     * parts however many they are, so the number of ways says nothing of how many parts there are.
     */
    record MoreWaysThanAreWrittenOut() implements WhyUnread {}

    /**
     * A part about a container holding more occurrences than a walk writes out, counted at every
     * level the walk passes. A figure of this compiler's work was reached — the one bounding how
     * far a container is written out, and not how many times a condition is read — and nothing is
     * said of the model.
     */
    record MoreElementsThanAreWrittenOut() implements WhyUnread {}

    /**
     * A part whose number is one of several — the answer of a case of a choice, a value a closure
     * is handed, a case of the definition a library operation is written in — that the reading did
     * not go into and read on each of them: it had gone into it already on the way here, or it
     * stands where no way in reaches.
     *
     * <p>No figure: nothing was counted. Whether going in is past a figure is answered where a
     * reading goes in, and said there as {@link MoreReadingsThanAreMade}.
     */
    record SeveralValuesNotGoneInto() implements WhyUnread {}

    /**
     * A construct met in several copies — a helper's, wherever the helper is written — whose copies
     * state different things, so the construct states none of them.
     */
    record CopiesStateDifferentThings() implements WhyUnread {}

    /** A construct the reading of what a body's conditions mean did not meet. */
    record NotMetByTheReading() implements WhyUnread {}

    /**
     * A statement about the elements of a container, or the steps of a walk, where what is stated
     * of one answers nothing on some rows — a quotient by what the element holds divides by nought
     * there — and which element a run stops at turns what the whole comes to, in an order nothing
     * here says.
     *
     * <p>The statement about each element is read. What the operation answers is not: where it
     * stops at the first element meeting the statement, a run reaching an element that answers
     * nothing before that one stops there, and where the row's order is not one the row writes
     * freely, nothing says which comes first.
     */
    record WhichElementARunStopsAt() implements WhyUnread {}
}
