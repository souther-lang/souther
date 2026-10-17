package souther.compiler.meaning;

import souther.compiler.observe.Figure;
import souther.compiler.partition.CompositionBudget;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * Why a reader of what a condition means did not take it into its own terms: what a row is asked
 * for, a column of a decision, what a path knows past a guard.
 *
 * <p>Three kinds, told apart by what it takes to lift one. The meaning was not read, which a rule of
 * the reading lifts; or it was read and the domain the reader writes in has no words for it, which
 * widening that domain lifts; or it was read, the domain has the words, and saying it in them took
 * more of this compiler's work than a figure lets, which raising the figure lifts. A meaning read
 * to the end and in the reader's words is taken, and
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
     * The figure of this compiler's work taking the condition stopped at, or none where it stopped
     * at none: the one place that says which, as {@link WhyUnread#figure} is for the reading.
     */
    default Optional<Figure> figure() {
        return switch (this) {
            case MeaningUnread(WhyUnread why) -> why.figure();
            case MoreWaysThanAreRead _ ->
                    Optional.of(CompositionBudget.READINGS_OF_ONE_CONDITION.figure());
            case MoreAlternativesThanAreTried _ ->
                    Optional.of(CompositionBudget.ALTERNATIVES_A_PATH_TRIES.figure());
            case MoreChoicesThanAreWrittenOut(CompositionBudget figure) ->
                    Optional.of(figure.figure());
            case OutsideDomain _ -> Optional.empty();
        };
    }

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
     * What the condition means was read and the reader has words for it, and taking it into them
     * stopped at a figure of this compiler's work: some or every element meeting it comes, taken
     * apart, to more ways an element may meet it than a reading of one condition makes. Raising the
     * figure lifts it; nothing about the model or about either domain does, so neither of the
     * other two is said of it.
     */
    record MoreWaysThanAreRead() implements WhyNotTaken {}

    /**
     * What the condition means was read and a path has words for it, and taking it into them
     * stopped at a figure of this compiler's work: one of several things holding is taken by
     * taking each alone and keeping the ones that leave something, and the parts taken alone in
     * one reading of the condition, however deep inside one another, came to more than are taken.
     * A part not taken may be the one that leaves nothing, so what the others came to is not
     * taken either. Raising the figure lifts it; the domain of what a path knows has the words,
     * so its limit is not said of it.
     */
    record MoreAlternativesThanAreTried() implements WhyNotTaken {}

    /**
     * What the condition means was read, and it holds a count of statements a reader takes by the
     * choices of which of them hold, and those were more than such a reader is handed, or written
     * out came to more parts ({@link CountsWrittenOut}). Raising the figure lifts
     * it; the count was read and stated whole, so nothing about its meaning is said.
     *
     * @param stoppedAt which of the two the choices were past
     */
    record MoreChoicesThanAreWrittenOut(CompositionBudget stoppedAt) implements WhyNotTaken {

        public MoreChoicesThanAreWrittenOut {
            Objects.requireNonNull(stoppedAt, "choices not written out were past some figure");
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
         * {@code a > b} over two cases of one sum is read perfectly, and what it comes to is a
         * difference between two positions that is a distance on nothing. What is here for an
         * author to act on is the carrier — a position whose values this compiler measures on
         * nothing is one every rule about it is unrepresented in.
         */
        A_QUANTITY_ON_NO_ORDER,

        /**
         * One of several things, or some element meeting something, as what a path knows: a path
         * knows a set of facts that all hold, and which of several holds, or which element, is no
         * fact of it. A limit of what a path knows and not of the propositions it is handed, which
         * state the alternatives in full.
         */
        A_PATH_KNOWS_NO_ALTERNATIVES,

        /**
         * What a dependency answered, asked of a row: a row writes the input, and stands a
         * dependency in with an answer rather than writing one, so what is asked of the answer is
         * a column of the decision the row is a row of and no demand on what it writes.
         */
        AN_ANSWER_A_ROW_STANDS_IN,

        /**
         * A node a search from a node reaches below the ones a row writes: a value holding values
         * of its own kind is written so deep and no deeper, so some node further down meeting what
         * the search asks is nothing a row is written toward. What it asks of the node it starts
         * at, and of that node having nothing below, is.
         */
        A_NODE_BELOW_WHAT_A_ROW_WRITES,

        /**
         * A place the tree a path is walked over does not read: a position, an answer or a value
         * the body bound that no expression of the condition stands for there, so there is no
         * subject for a fact about it to be about.
         */
        A_PLACE_THE_PATH_DOES_NOT_READ,

        /**
         * A value being none of some cases, as what a path knows: a path keeps which cases a value
         * may still be, and the rest of what its type divides into is not read where it takes one
         * in.
         */
        A_PATH_KNOWS_NO_CASE_A_VALUE_IS_NOT,

        /** Two values being one, as what a path knows, which is no relation of numbers. */
        A_PATH_KNOWS_NO_SAMENESS_OF_VALUES,

        /** A place on an order that is no number, where no range says it: a value other than a
         *  written place, which leaves a hole rather than a range, and a quantity that is no value
         *  of the input. A value of the input at or past a written place is a range, and a path
         *  holds it. */
        A_PATH_KNOWS_NO_PLACE_ON_AN_ORDER,

        /** How many elements of a container meet something, as what a path knows: no subject of
         *  the tree it walks is that count. */
        A_PATH_KNOWS_NO_COUNT_OF_ELEMENTS,

        /** A number taken over the elements of a container — how many different values they come
         *  to, or what a number of each adds up to — as what a path knows: no subject of the tree
         *  it walks is that number. */
        A_PATH_KNOWS_NO_NUMBER_OVER_ELEMENTS,

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
        A_NUMBER_THE_PATH_CANNOT_HOLD;

        /**
         * Whose domain stops here: the one each limit names, said where the limit is declared so
         * that a limit added is a domain chosen, and a reader held to its own limits is held to
         * this answer rather than to a list kept beside it.
         */
        public Domain domain() {
            return switch (this) {
                case A_QUANTITY_ON_NO_ORDER, AN_ANSWER_A_ROW_STANDS_IN,
                     A_NODE_BELOW_WHAT_A_ROW_WRITES ->
                        Domain.WHAT_A_ROW_IS_WRITTEN_IN;
                case A_PATH_KNOWS_NO_ALTERNATIVES, A_PLACE_THE_PATH_DOES_NOT_READ,
                     A_PATH_KNOWS_NO_CASE_A_VALUE_IS_NOT, A_PATH_KNOWS_NO_SAMENESS_OF_VALUES,
                     A_PATH_KNOWS_NO_PLACE_ON_AN_ORDER, A_PATH_KNOWS_NO_COUNT_OF_ELEMENTS,
                     A_PATH_KNOWS_NO_NUMBER_OVER_ELEMENTS, A_PATH_HOLDS_ELEMENT_FACTS_AS_WRITTEN,
                     A_NUMBER_THE_PATH_CANNOT_HOLD ->
                        Domain.WHAT_A_PATH_KNOWS;
            };
        }

        /** The domains a reader writes in, each of which a limit is the edge of. */
        public enum Domain {

            /** The input's positions, which a row is written at. */
            WHAT_A_ROW_IS_WRITTEN_IN,

            /** Relations of numbers, truths and what every element was written to meet, about
             *  the places of the tree a path walks. */
            WHAT_A_PATH_KNOWS
        }
    }
}
