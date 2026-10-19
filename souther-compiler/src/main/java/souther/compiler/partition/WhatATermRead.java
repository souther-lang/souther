package souther.compiler.partition;

import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;

/**
 * What one term of a quantity came to at one row: the number it names, or why it names none.
 *
 * <p>The arms every reading of a term ends in, rather than {@link NumericTerm.Reading}'s. A walk
 * that was not taken is one of the ways a term comes to no number and is not a reading of a value,
 * so it has no arm there — and each of the quantities would otherwise carry its own guard for that
 * before asking, which is one rule written as many times as there are quantities.
 *
 * <p>Made here and nowhere else. What a walk answered and what a term reads of a value are put
 * together in one place, so the arms below are the whole of what a quantity has to answer for, and
 * a quantity that met something new is one this file has been taught about.
 *
 * <p><b>Every reader switches over these.</b> The point of the arms is that a quantity says what it
 * does about each; read with a chain of tests ending in a fall-through, an arm added later would
 * quietly take whatever the last line does, which is how a term that could not be read came to be
 * answered as a row standing somewhere else.
 */
sealed interface WhatATermRead {

    /** The number the term names at this row. */
    record Number(Place value) implements WhatATermRead {

        public Number {
            Objects.requireNonNull(value, "a term that names a number names one");
        }
    }

    /** The value was read and this term is no number of it, which is an answer about the value and
     *  not about anything that stopped. */
    record NoNumberOfTheValue() implements WhatATermRead { }

    /**
     * The row wrote nothing at the term's position under this reading, so this quantity has no
     * value at this reading of the row: either it put no element there at all, or it put them
     * only under elements this reading did not choose — an element of another case of a sum among
     * them — and another reading of the row is where those are.
     *
     * <p>Which settles the reading rather than leaving it open, and settles it whatever else the
     * quantity met. A number over a position a row put nothing at is a number the row does not
     * have, and it does not have it any more once a wider run keeps what it shortened elsewhere —
     * so a reading stopped at another term is not what a reader is told about this row.
     */
    record NothingWrittenThere() implements WhatATermRead { }

    /** No number, and this is what the reading met instead. */
    record CameToNothing(ReadingGap why) implements WhatATermRead {

        public CameToNothing {
            Objects.requireNonNull(why, "a reading that came to nothing says what it met");
        }
    }

    /** What {@code on} reads where the walk to its one position came to {@code answered}. */
    static WhatATermRead at(TermOrders on, WalkResult<ObservationAtPoint> answered) {
        return switch (answered) {
            case WalkResult.CouldNotWalk<ObservationAtPoint> _ ->
                    new CameToNothing(ReadingGap.COULD_NOT_WALK);
            case WalkResult.Reached(ObservationAtPoint standing) -> switch (standing) {
                case ObservationAtPoint.Value(ObservedValue value) -> of(on.read(value));
                // A fact about the row, which answers for it. The row was read and put no element
                // here, or put them only under elements another reading chose, so this quantity has
                // no value at it under this reading -- and reporting that as a reading that came to
                // nothing leaves a point undecided over a row that plainly settles it, every one of
                // its readings being tried.
                case ObservationAtPoint.WroteNothing _,
                     ObservationAtPoint.BelongsToAnotherReading _ -> new NothingWrittenThere();
            };
        };
    }

    /**
     * What {@code on} reads of the element {@code row} chose in the container its term is taken
     * over, among the elements of the occurrence of that container it chose it in: how often the
     * element's value occurs, or the end of its key's values.
     *
     * <p>Of one occurrence and of nothing gathered beside it. The values standing at a place inside
     * a container are every occurrence's ({@link BorderQuantity.Observation#everyValueAt}), and two
     * orders each holding lines are two sets of lines: a line of one is no neighbour of a line of
     * the other. So the elements are those of the occurrence the reading is in ({@link
     * BorderQuantity.Observation#eachElementOf}, under whatever the reading chose of every other
     * container), each read with it chosen, so a field one element holds is paired with that
     * element's others; and the element under consideration is the one the reading chose, read
     * off the reading itself.
     *
     * <p>A walk that cannot reach the occurrence could not walk to a number; a reading that chose
     * no element of the container holds nothing at the element's place, which is the row's own
     * answer. Only the fields the number's reading asks for are looked at, so what stopped the
     * first of those is what the row is told, and a field of an element nothing asked about stops
     * nothing.
     *
     * <p>The elements are put together once for every reading of the occurrence
     * ({@link BorderQuantity.Observation#keptOf}), since what each of them holds does not turn on
     * which of them a reading chose; each reading asks the number of its own element.
     */
    static WhatATermRead inItsOccurrence(TermOrders on, BorderQuantity.Observation row) {
        TermPath element = on.amongItsNeighbours().container().element();
        return switch (row.keptOf(new ItsNeighbours(on))) {
            case WalkResult.CouldNotWalk<TermOrders.ElementsTogether<WhatATermRead>> _ ->
                    new CameToNothing(ReadingGap.COULD_NOT_WALK);
            case WalkResult.Reached(TermOrders.ElementsTogether<WhatATermRead> together) ->
                    switch (together.numberOf(heldBy(row, element))) {
                        case TermOrders.Neighbouring.Read<WhatATermRead>(
                                NumericTerm.Reading read) -> of(read);
                        // A field the row gave nothing at is what the row is told, whatever the
                        // reading made of the rest.
                        case TermOrders.Neighbouring.HeldNothing<WhatATermRead>(
                                WhatATermRead why) -> why;
                    };
        };
    }

    /**
     * The elements of the occurrence of a container a reading is in, put together for a number of
     * an element read off its neighbours.
     */
    record ItsNeighbours(TermOrders on) implements
            BorderQuantity.ReadAlike<WalkResult<TermOrders.ElementsTogether<WhatATermRead>>> {

        @Override
        public WalkResult<TermOrders.ElementsTogether<WhatATermRead>> readAt(
                BorderQuantity.Observation reading) {
            TermPath container = on.amongItsNeighbours().container();
            if (!(reading.eachElementOf(container) instanceof WalkResult.Reached<
                    List<BorderQuantity.Observation>>(List<BorderQuantity.Observation> elements))) {
                return WalkResult.couldNotWalk();
            }
            List<Function<ElementProjection, TermOrders.Holding<WhatATermRead>>> each =
                    new ArrayList<>(elements.size());
            for (BorderQuantity.Observation one : elements) {
                each.add(heldBy(one, container.element()));
            }
            return WalkResult.reached(on.together(each));
        }
    }

    /**
     * What {@code row} holds at each field of the element at {@code element}: a value, or why it
     * holds none in this layer's words — a walk that could not reach the field, or a row that wrote
     * nothing there under this reading.
     */
    private static Function<ElementProjection, TermOrders.Holding<WhatATermRead>> heldBy(
            BorderQuantity.Observation row, TermPath element) {
        return field -> switch (row.at(field.from(element))) {
            case WalkResult.CouldNotWalk<ObservationAtPoint> _ ->
                    new TermOrders.Holding.Nothing<>(new CameToNothing(ReadingGap.COULD_NOT_WALK));
            case WalkResult.Reached(ObservationAtPoint standing) -> switch (standing) {
                case ObservationAtPoint.Value(ObservedValue value) ->
                        new TermOrders.Holding.Value<>(value);
                case ObservationAtPoint.WroteNothing _,
                     ObservationAtPoint.BelongsToAnotherReading _ ->
                        new TermOrders.Holding.Nothing<>(new NothingWrittenThere());
            };
        };
    }

    /**
     * The same over the values of a run, which a walk that was not taken has none of.
     *
     * <p>Every value standing at the run's path, whichever elements a reading chose, so one
     * reading of the run answers every reading of the row.
     */
    static WhatATermRead over(TermOrders on, BorderQuantity.Observation row, TermPath subject) {
        return row.keptOf(new ARun(on, subject));
    }

    /**
     * What {@code on} reads of the value this reading chose at {@code place}, among every value
     * the row wrote there: how often that value occurs in all the containers the place stands in.
     *
     * <p>The value is the reading's own and the values it is counted among are every occurrence's,
     * whichever a reading chose, so a row that wrote nothing at the place has no value for the
     * number and a place the walk could not reach has none to read.
     */
    static WhatATermRead amongEveryOccurrence(TermOrders on, BorderQuantity.Observation row,
                                              TermPath place) {
        KeptOccurrences kept = ((NumericTerm.OccurrencesOfItsValue) on.term()).selection();
        if (kept != null) {
            return amongTheKept(on, row, place, kept);
        }
        return switch (row.at(place)) {
            case WalkResult.CouldNotWalk<ObservationAtPoint> _ ->
                    new CameToNothing(ReadingGap.COULD_NOT_WALK);
            case WalkResult.Reached(ObservationAtPoint standing) -> switch (standing) {
                case ObservationAtPoint.Value(ObservedValue own) -> switch (
                        row.keptOf(new EveryValue(place))) {
                    case WalkResult.CouldNotWalk<List<ObservedValue>> _ ->
                            new CameToNothing(ReadingGap.COULD_NOT_WALK);
                    case WalkResult.Reached(List<ObservedValue> values) ->
                            of(on.readAmong(own, values));
                };
                case ObservationAtPoint.WroteNothing _,
                     ObservationAtPoint.BelongsToAnotherReading _ -> new NothingWrittenThere();
            };
        };
    }

    /**
     * The same among the occurrences the elements are kept for, in the one occurrence of the
     * container the reading is in: the value this reading chose is counted among the values of
     * the elements that meet the statement, and it is itself one of them or the reading has no
     * number.
     *
     * <p>A reading that chose an element the statement drops is a reading of the row at which no
     * entry stands, which is the row's own answer; one the statement could not be put to is a
     * reading that could not be made.
     */
    private static WhatATermRead amongTheKept(TermOrders on, BorderQuantity.Observation row,
                                              TermPath place, KeptOccurrences kept) {
        if (!(row.at(place) instanceof WalkResult.Reached<ObservationAtPoint>(
                ObservationAtPoint standing))) {
            return new CameToNothing(ReadingGap.COULD_NOT_WALK);
        }
        if (!(standing instanceof ObservationAtPoint.Value(ObservedValue own))) {
            return new NothingWrittenThere();
        }
        WhatATermRead ownKept = keptOrNot(kept.perElement().at(row));
        if (ownKept != null) {
            return ownKept;
        }
        TheKept theKept = row.keptOf(new TheKeptValues(kept, place));
        return theKept.stopped() != null ? theKept.stopped()
                : of(on.readAmong(own, theKept.values()));
    }

    /** Every value the row wrote at {@code place}, which no reading's choice turns. */
    record EveryValue(TermPath place)
            implements BorderQuantity.ReadAlike<WalkResult<List<ObservedValue>>> {

        @Override
        public WalkResult<List<ObservedValue>> readAt(BorderQuantity.Observation row) {
            return row.everyValueAt(place);
        }
    }

    /**
     * The values at {@code place} of the occurrences {@code kept} keeps, or what stopped them
     * being read.
     *
     * @param values  the kept occurrences' values, in the order the row wrote them
     * @param stopped why they could not be read, or null where they were
     */
    record TheKept(List<ObservedValue> values, WhatATermRead stopped) {}

    /**
     * The kept occurrences' values, which no reading's choice turns: every reading of a row asks
     * them of the same occurrences, and a row has a reading per element.
     */
    record TheKeptValues(KeptOccurrences kept, TermPath place)
            implements BorderQuantity.ReadAlike<TheKept> {

        @Override
        public TheKept readAt(BorderQuantity.Observation row) {
            // Each container the place stands in, the outer one first, is read under each element
            // of the one outside it: the occurrences are those of every one of them.
            List<BorderQuantity.Observation> elements = List.of(row);
            for (TermPath container : place.containersHoldingIt()) {
                List<BorderQuantity.Observation> inside = new ArrayList<>();
                for (BorderQuantity.Observation outer : elements) {
                    if (!(outer.eachElementOf(container) instanceof WalkResult.Reached<
                            List<BorderQuantity.Observation>>(
                                    List<BorderQuantity.Observation> each))) {
                        return stoppedAt(ReadingGap.COULD_NOT_WALK);
                    }
                    inside.addAll(each);
                }
                elements = inside;
            }
            List<ObservedValue> values = new ArrayList<>();
            for (BorderQuantity.Observation element : elements) {
                AStatementAtARow.Answer answer = kept.perElement().at(element);
                if (answer instanceof AStatementAtARow.Answer.CouldNotTell(var why)) {
                    return stoppedAt(why.iterator().next());
                }
                if (!(answer instanceof AStatementAtARow.Answer.Holds)) {
                    continue;
                }
                if (!(element.at(place) instanceof WalkResult.Reached<ObservationAtPoint>(
                        ObservationAtPoint.Value(ObservedValue value)))) {
                    return stoppedAt(ReadingGap.COULD_NOT_WALK);
                }
                values.add(value);
            }
            return new TheKept(values, null);
        }

        private static TheKept stoppedAt(ReadingGap gap) {
            return new TheKept(List.of(), new CameToNothing(gap));
        }
    }

    /** Null where the statement holds of the element, and what the reading comes to where it
     *  does not or could not be put. */
    private static WhatATermRead keptOrNot(AStatementAtARow.Answer answer) {
        return switch (answer) {
            case AStatementAtARow.Answer.Holds _ -> null;
            case AStatementAtARow.Answer.Fails _ -> new NothingWrittenThere();
            case AStatementAtARow.Answer.CouldNotTell(var why) ->
                    new CameToNothing(why.iterator().next());
        };
    }

    /** A run read of every value at {@code subject}, which no reading's choice turns. */
    record ARun(TermOrders on, TermPath subject)
            implements BorderQuantity.ReadAlike<WhatATermRead> {

        @Override
        public WhatATermRead readAt(BorderQuantity.Observation reading) {
            return switch (reading.everyValueAt(subject)) {
                case WalkResult.CouldNotWalk<List<ObservedValue>> _ ->
                        new CameToNothing(ReadingGap.COULD_NOT_WALK);
                case WalkResult.Reached(List<ObservedValue> values) -> of(on.readOver(values));
            };
        }
    }

    /**
     * What {@code on} reads of a run computed of each element of the container {@code row} wrote.
     *
     * <p>Element by element, each read as the row with that element chosen, so the fields one
     * computation reads are the fields of one element. A field is looked at only where the
     * computation asks for it: a field the row wrote nothing at is a row that has no value for the
     * run where the computation needs it, and says nothing where the element's own choice does not
     * reach it. What stopped the first element that could not be read is what the row is told.
     *
     * <p>Read once for every reading of the container the run is computed over, whose elements
     * are all of them whichever a reading chose.
     */
    static WhatATermRead overElements(TermOrders on, RunSource.ComputedOccurrences computed,
                                      BorderQuantity.Observation row) {
        return row.keptOf(new ARunOfEachElement(on, computed));
    }

    /** A run computed of each element of a container. */
    record ARunOfEachElement(TermOrders on, RunSource.ComputedOccurrences computed)
            implements BorderQuantity.ReadAlike<WhatATermRead> {

        @Override
        public WhatATermRead readAt(BorderQuantity.Observation reading) {
            TermPath container = computed.elements().outermostContainer();
            if (!(reading.eachElementOf(container)
                    instanceof WalkResult.Reached<List<BorderQuantity.Observation>> reached)) {
                return new CameToNothing(ReadingGap.COULD_NOT_WALK);
            }
            WhatRowsLeft left = new WhatRowsLeft();
            List<Function<ElementProjection, ObservedValue>> each = new ArrayList<>();
            for (BorderQuantity.Observation element : reached.value()) {
                each.add(field -> left.at(element, field.from(computed.elements())));
            }
            NumericTerm.Reading read = on.readOverElements(each);
            return left.stopped() != null ? left.stopped() : of(read);
        }
    }

    /**
     * Why the row could not be read at a field, for the first one it could not.
     *
     * <p>Kept beside the reading and not inside it, which answers a field it cannot use as no value
     * and goes no further: what the row did there is in this layer's words.
     */
    final class WhatRowsLeft {

        private WhatATermRead stopped;

        /** The value at {@code path}, or null with why recorded where the row gives none. */
        ObservedValue at(BorderQuantity.Observation element, TermPath path) {
            switch (element.at(path)) {
                case WalkResult.CouldNotWalk<ObservationAtPoint> _ ->
                        stop(new CameToNothing(ReadingGap.COULD_NOT_WALK));
                case WalkResult.Reached(ObservationAtPoint standing) -> {
                    switch (standing) {
                        case ObservationAtPoint.Value(ObservedValue value) -> {
                            return value;
                        }
                        case ObservationAtPoint.WroteNothing _,
                             ObservationAtPoint.BelongsToAnotherReading _ ->
                                stop(new NothingWrittenThere());
                    }
                }
            }
            return null;
        }

        private void stop(WhatATermRead why) {
            if (stopped == null) {
                stopped = why;
            }
        }

        WhatATermRead stopped() {
            return stopped;
        }
    }

    /** What a term's own reading of a value comes to here. */
    private static WhatATermRead of(NumericTerm.Reading read) {
        return switch (read) {
            case NumericTerm.Reading.Number(Place value) -> new Number(value);
            case NumericTerm.Reading.Missing(Incompleteness.Cause cause) ->
                    new CameToNothing(ReadingGap.of(cause));
            case NumericTerm.Reading.NotNumber _ -> new NoNumberOfTheValue();
            case NumericTerm.Reading.NotWorkedOut(UnheldNumber why) ->
                    new CameToNothing(ReadingGap.of(why));
        };
    }
}
