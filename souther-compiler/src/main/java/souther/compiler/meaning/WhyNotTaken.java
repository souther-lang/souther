package souther.compiler.meaning;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * Why a reader of what a condition means did not take it into its own terms: what a row is asked
 * for, a column of a decision, what a path knows past a guard.
 *
 * <p>Two kinds, told apart by what it takes to lift one. The meaning was not read, which a rule of
 * the reading lifts; or it was read and the domain the reader writes in has no words for it, which
 * widening that domain lifts. A meaning read to the end and in the reader's words is taken, and
 * whether a row can then be built for it is no part of this: a composer that writes nothing
 * toward a demand says so where rows are composed, beside the demand it was handed. None of these
 * says a row cannot be written, and one going away is a capability gained rather than a model
 * changed.
 *
 * <p>One reason each, and a reader keeps every one it met. A condition made of parts can be
 * declined for one reason in one part and another in the next — one part's meaning unread, the
 * whole a shape the reader has no words for — and each is a different thing for somebody to do,
 * so none stands in for another.
 */
public sealed interface WhyNotTaken {

    /**
     * Why a reader declined all of {@code declined} without asking its parts: {@code because}, and
     * what stopped the meaning of every part of it nothing read.
     *
     * <p>Two scopes. Where the meaning stopped is the proposition's and not the reader's, so it is
     * said by whoever declines it, however far down the part stands. What the reader would have
     * said of a part is the reader's, and of a part it never asked it is not made up.
     */
    static List<WhyNotTaken> declinedWhole(WhyNotTaken because, Proposition declined) {
        Set<WhyNotTaken> out = new LinkedHashSet<>();
        out.add(because);
        Proposition.stopsIn(declined).forEach(why -> out.add(new MeaningUnread(why)));
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
     * Where a reader's domain has no words for what a condition means.
     *
     * <p>Each names the reader whose domain it is. What a row is asked is written at the input's
     * positions; what a path knows is relations of numbers, truths and what the elements of a
     * container were written to meet, about the places of the tree it walks. The proposition
     * language says every one of these; a limit here is where one of those two domains stops.
     */
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
         * fact of it. A limit of what a path knows and not of the propositions it is handed, which
         * state the alternatives in full.
         */
        A_PATH_KNOWS_NO_ALTERNATIVES,

        /**
         * A position of the input the reading of it holds no place for: one under a value the
         * reading does not descend into, so nothing a row writes stands there to be narrowed.
         */
        A_POSITION_THE_READING_HOLDS_NO_PLACE_FOR,

        /**
         * What a dependency answered, asked of a row: a row writes the input, and stands a
         * dependency in with an answer rather than writing one, so what is asked of the answer is
         * a column of the decision the row is a row of and no demand on what it writes.
         */
        AN_ANSWER_A_ROW_STANDS_IN,

        /**
         * A place the tree a path is walked over does not read: a position, an answer or a value
         * the body bound that no expression of the condition stands for there, so there is no
         * subject for a fact about it to be about.
         */
        A_PLACE_THE_PATH_DOES_NOT_READ,

        /**
         * Which case a value is, or whether an optional holds one, as what a path knows: a path
         * knows relations of numbers and truths, and which arm a value takes is decided by the
         * fork that enters it rather than kept as a fact.
         */
        A_PATH_KNOWS_NO_CASES,

        /** Two values being one, as what a path knows, which is no relation of numbers. */
        A_PATH_KNOWS_NO_SAMENESS_OF_VALUES,

        /** A place on an order that is no number, as what a path knows. */
        A_PATH_KNOWS_NO_PLACE_ON_AN_ORDER,

        /** How many elements of a container meet something, as what a path knows: no subject of
         *  the tree it walks is that count. */
        A_PATH_KNOWS_NO_COUNT_OF_ELEMENTS,

        /**
         * Every element of a container meeting something, as what a path knows: a path holds what
         * every element meets as the closure the quantifier was written with, so that it can be
         * read again at the element another closure is handed, and a statement read off the
         * meaning is no closure.
         */
        A_PATH_HOLDS_ELEMENT_FACTS_AS_WRITTEN,

        /**
         * A relation of numbers whose form over the places a path reads has a weight its exact
         * arithmetic could not hold: two numbers of the statement are one value there, and what
         * their weights add to is a number this compiler had no room for or that has no exact
         * representation at all. The statement was read to the end; what stops is the number a
         * path would keep the fact in.
         */
        A_NUMBER_THE_PATH_CANNOT_HOLD
    }
}
