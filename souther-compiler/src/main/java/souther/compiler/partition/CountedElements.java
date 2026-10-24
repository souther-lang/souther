package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.UnheldNumber;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * What a count of the elements of a container is of: the container, what an element is counted for
 * meeting, and that statement as rows are asked it.
 *
 * <p>Apart from the quantity a line on the count is drawn on. A row composed for a count, a
 * condition on the way that holds one against a number and a line on it all ask what is counted,
 * and only the last is a quantity a border stands on; held as the quantity, every one of them would
 * be a reader asking which quantity a border is on.
 *
 * @param behavior         the behavior whose input the container is in
 * @param container        the container the elements are counted in
 * @param meeting          what an element is counted for meeting, over the element's own numbers
 *                         and the input's
 * @param perElement       {@code meeting} put to rows, which is what an element is asked
 * @param on               the order each number {@code perElement} reads is written on, where the
 *                         input's reading has one
 * @param anElementMeeting what an element meeting {@code meeting} is held to, as relations a
 *                         region is narrowed by, where it is that
 *                         ({@link DemandReading#anElementMeeting})
 * @param handedOn         what another container is asked about an element meeting
 *                         {@code meeting}, where that is all it is: the one demand an element
 *                         meets by what that container holds ({@link ACountHandedOn})
 * @param differentAt      where the value each element holds stands — one place, or the place its
 *                         case chooses — where what is counted is how many different values the
 *                         elements meeting {@code meeting} hold there rather than how many of
 *                         them there are ({@link Quantity.HowManyDifferentMeet})
 * @param across           the container inside each element of which a container at
 *                         {@code container} stands, where the values counted are those of every
 *                         element of all of them put end to end and not of the one a reading
 *                         chose ({@link Quantity.HowManyDifferentMeet#across})
 */
record CountedElements(String behavior, TermPath container, Proposition meeting,
                       AStatementAtARow perElement, Map<NumericTerm, Carrier> on,
                       Optional<List<TakenConstraint>> anElementMeeting,
                       Optional<RowDemand.WithinIt> handedOn,
                       Optional<Quantity.TheValue> differentAt, Optional<TermPath> across) {

    CountedElements {
        if (behavior == null || container == null || meeting == null || perElement == null
                || anElementMeeting == null || handedOn == null || differentAt == null
                || across == null) {
            throw new IllegalArgumentException("a count is a behavior's count of the elements of"
                    + " some container meeting something");
        }
        if (differentAt.isPresent() && !(differentAt.get().where()
                instanceof DecisionSubject.AnInput(TermPath where)
                && where.isAtOrUnder(container.element()))) {
            throw new IllegalArgumentException("the values counted are of the elements of "
                    + container + ", and " + differentAt.get() + " is none of theirs");
        }
        if (across.isPresent() && (differentAt.isEmpty()
                || !container.isAtOrUnder(across.get().element())
                || container.containersHoldingIt().size()
                        != across.get().containersHoldingIt().size() + 1)) {
            throw new IllegalArgumentException("the values of every element of the containers at "
                    + container + " are counted, one inside each element of " + across.get());
        }
        on = Map.copyOf(on);
        anElementMeeting = anElementMeeting.map(List::copyOf);
    }

    /**
     * How many elements of {@code count}'s container meet its statement, as {@code behavior} reads
     * it, for a statement {@link AStatementAtARow#askable} says a row can be asked — or, where
     * {@code count} is how many different values those hold ({@link
     * Quantity.HowManyDifferentMeet}), the count of those elements with each value counted once.
     * {@code count} is one {@link AStatementAtARow#countIn} answers.
     *
     * <p>The one way one of these is made, wherever the count is met: a line drawn on it and a
     * condition on the way to another are the same count where they count the same thing.
     *
     * @param anElementMeeting what an element meeting the statement asks, as the reading of a
     *                         condition that some element meets it comes to
     */
    static CountedElements of(String behavior, Quantity count, Quantities quantities,
                              AnElementMeeting anElementMeeting) {
        Identity identity = identityOf(behavior, count);
        AStatementAtARow perElement =
                AStatementAtARow.of(identity.meeting(), identity.behavior(), quantities);
        Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
        for (NumericTerm each : perElement.numbers()) {
            TermOrders orders = quantities.ordersOf(each);
            if (orders != null && orders.observed() != null && orders.answered() != null) {
                on.put(each, orders.answered());
            }
        }
        return new CountedElements(identity.behavior(), identity.container(), identity.meeting(),
                perElement, on, anElementMeeting.heldTo(), anElementMeeting.handedOn(),
                identity.differentAt(), identity.across());
    }

    /**
     * What this counts at {@code row}: how many elements meet the statement, or how many
     * different values those elements hold where that is what is counted.
     *
     * @return null where the walk could not reach the container
     */
    AStatementAtARow.HowManyAtARow at(BorderQuantity.Observation row) {
        return perElement.howManyIn(container, differentAt, across, row);
    }

    /** Asks {@code row} for the containers this counts the elements of, as the walk finding
     *  which containers a row chooses an element of asks. */
    void lookAt(BorderQuantity.Observation row) {
        AStatementAtARow.lookAtTheElementsIn(row, container, across);
        Set<TermPath> together = new LinkedHashSet<>();
        together.add(container);
        across.ifPresent(together::add);
        perElement.lookAt(row, together);
    }

    /** Every number of a row the statement reads, the element's own among them. */
    List<NumericTerm> numbers() {
        return perElement.numbers();
    }

    /** The counts there are: every whole number, from none. */
    LevelSpace levels() {
        return LevelSpace.steppingBy(ExactRatio.ONE);
    }

    /**
     * Which count this is, apart from what reading it worked out.
     *
     * <p>Two readings of one count may read its statement to different depths — one finds what an
     * element meeting it is held to and another does not — and they are still one count. What a
     * row is asked of a count is gathered by this, and never by what a reading made of it.
     */
    record Identity(String behavior, TermPath container, Proposition meeting,
                    Optional<Quantity.TheValue> differentAt, Optional<TermPath> across) {}

    /** Which count this is ({@link Identity}). */
    Identity identity() {
        return new Identity(behavior, container, meeting, differentAt, across);
    }

    /**
     * Which count {@code count}, one {@link AStatementAtARow#countIn} answers, read in
     * {@code behavior} is, with nothing about it worked out — the identity {@link #of} would give
     * it.
     *
     * <p>Of how many different values the elements meeting a statement hold whatever the statement
     * was asked of. One asked of what the elements holding a value come to answers alike for each
     * of them, so a value is counted where some element holding it meets it, which is the count of
     * it asked of each element.
     */
    static Identity identityOf(String behavior, Quantity count) {
        Quantity.HowManyMeet elements = AStatementAtARow.elementsOf(count);
        return new Identity(behavior, elements.container().inputPosition(),
                elements.ofTheElement(), AStatementAtARow.differentAt(count),
                AStatementAtARow.acrossOf(count));
    }

    /**
     * This count as both readings of it read it: what an element meeting the statement is held to,
     * wherever either reading worked that out.
     *
     * <p>Both and not the first. Each reading that works it out reads the whole statement as the
     * relations an element meeting it is held to, so either is what the statement says and the two
     * together say it too; which of them came first is the order conditions were written in, and
     * what a row is composed with does not turn on that.
     */
    CountedElements and(CountedElements other) {
        if (!identity().equals(other.identity())) {
            throw new IllegalArgumentException(
                    "two readings of one count, and these are " + this + " and " + other);
        }
        Optional<List<TakenConstraint>> both;
        if (anElementMeeting.isEmpty() || other.anElementMeeting.isEmpty()) {
            both = anElementMeeting.isPresent() ? anElementMeeting : other.anElementMeeting;
        } else {
            Set<TakenConstraint> union = new LinkedHashSet<>(anElementMeeting.get());
            union.addAll(other.anElementMeeting.get());
            both = Optional.of(List.copyOf(union));
        }
        // One statement handed on is one demand however it was read; a reading that found it is
        // the one kept.
        return new CountedElements(behavior, container, meeting, perElement, on, both,
                handedOn.isPresent() ? handedOn : other.handedOn, differentAt, across);
    }

    /**
     * The least count {@code region} holds: one of them, none at all, or one that could not be
     * worked out.
     *
     * <p>Three answers and not a count or a null. That the region holds no count is a proof — no
     * container meets what it asks — and that its least count could not be held is nothing of the
     * kind; folded into one null, a reader proving the first was proving it of the second.
     */
    Least leastIn(LevelRegion region) {
        LevelRegion counts = region.meet(LevelRegion.of(new LevelInterval(
                Bound.at(new Level.OfTheQuantity(ExactRatio.ZERO), true), null)));
        Level least = null;
        UnheldNumber unheld = null;
        for (LevelInterval part : counts.parts()) {
            switch (levels().inspect(part)) {
                case Occupancy.Empty _ -> { }
                case Occupancy.Inhabited(Level first, Level _) -> {
                    if (least == null
                            || first.asAnExactNumber().compareTo(least.asAnExactNumber()) < 0) {
                        least = first;
                    }
                }
                case Occupancy.NotWorkedOut(UnheldNumber why) -> unheld = why;
            }
        }
        if (least == null) {
            return unheld == null ? new Least.None() : new Least.NotWorkedOut(unheld);
        }
        return switch (Count.written(least.asAnExactNumber())) {
            case ExactAnswer.Held<Optional<Count>>(Optional<Count> written) ->
                    written.<Least>map(Least.At::new).orElseGet(
                            () -> new Least.NotWorkedOut(UnheldNumber.NO_REPRESENTATION_EXISTS));
            case ExactAnswer.Unheld<Optional<Count>> notHeld ->
                    new Least.NotWorkedOut(notHeld.why());
        };
    }

    /** What the least count of a region came to ({@link #leastIn}). */
    sealed interface Least {

        /** The least count the region holds. */
        record At(Count count) implements Least {}

        /** The region holds no count: no container has so many elements meeting the statement. */
        record None() implements Least {}

        /** A count of the region could not be worked out, which says nothing of whether it holds
         *  one. */
        record NotWorkedOut(UnheldNumber why) implements Least {}
    }

    /**
     * Places for every number the statement reads beside an element, chosen together, and where
     * {@code oneMeets}, together with an element that meets the statement.
     *
     * <p>Together, because what the numbers beside an element are asked is whether some element
     * meets the statement with them standing there, and that is one question about all of them:
     * chosen one at a time, {@code x > a && x < b} took {@code a} and {@code b} at one value and
     * no element was between them. So the region is narrowed by what an element meeting the
     * statement is held to, and the element's own number is placed with the rest by the search
     * that places every condition's numbers on the way to a point ({@link NumericWitness}). The
     * element's place is not handed on: which elements the container holds is the composing's.
     *
     * <p>Where what an element meeting the statement is held to was not read as relations, the
     * numbers beside it are placed in the region as it is, and the composing finds out whether an
     * element meets the statement with them.
     */
    NumericWitness.Standing placesBeside(SearchRegion within, boolean oneMeets,
                                         WitnessSearch looking) {
        List<NumericTerm.FromOnePosition> placed = new ArrayList<>();
        for (NumericTerm term : numbers()) {
            if (!term.subjectPath().insideAContainer() && term.atOnePosition() != null) {
                placed.add(term.atOnePosition());
            }
        }
        SearchRegion region = within;
        if (oneMeets && anElementMeeting.isPresent()) {
            for (TakenConstraint each : anElementMeeting.get()) {
                region = each.narrowing(region);
                for (NumericTerm term : each.terms()) {
                    if (term.atOnePosition() != null && !placed.contains(term.atOnePosition())) {
                        placed.add(term.atOnePosition());
                    }
                }
            }
        }
        return NumericWitness.of(region, placed, on::get, looking);
    }

    /**
     * A count as it is written: {@code #container [statement]}, and, where it is how many
     * different values stand at {@code differentAt} over the elements meeting the statement,
     * {@code #different container [place] where [statement]} — the container being the one whose
     * elements hold the containers, where the values are of every element of those
     * ({@code across}), as the quantity is written.
     */
    static String spelled(TermPath container, Optional<Quantity.TheValue> differentAt,
                          Optional<TermPath> across, String statement) {
        return differentAt.map(at -> "#different " + across.orElse(container) + " ["
                        + at.spelled() + "] where ")
                .orElse("#" + container + " ") + "[" + statement + "]";
    }

    @Override
    public String toString() {
        return spelled(container, differentAt, across, meeting.key());
    }
}
