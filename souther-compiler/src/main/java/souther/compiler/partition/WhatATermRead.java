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
     * The row wrote nothing at the term's position, so this quantity has no value at this row.
     *
     * <p>Which settles the row rather than leaving it open, and settles it whatever else the
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
                // here, so this quantity has no value at it -- and reporting that as a reading that
                // came to nothing leaves a point undecided over a row that plainly settles it.
                case ObservationAtPoint.WroteNothing _ -> new NothingWrittenThere();
                // The row's values here are under elements another reading chose. The walk arrived
                // and none of this row's values stands here under this one, which is the reading
                // coming to nothing and is what the word is for.
                case ObservationAtPoint.BelongsToAnotherReading _ ->
                        new CameToNothing(ReadingGap.NO_VALUE);
            };
        };
    }

    /**
     * What {@code on} reads at the place the element {@code row} has chosen stands at, among every
     * value the elements of its container hold there: how often the element's own value occurs.
     */
    static WhatATermRead among(TermOrders on, BorderQuantity.Observation row, TermPath place) {
        return switch (row.at(place)) {
            case WalkResult.CouldNotWalk<ObservationAtPoint> _ ->
                    new CameToNothing(ReadingGap.COULD_NOT_WALK);
            case WalkResult.Reached(ObservationAtPoint standing) -> switch (standing) {
                case ObservationAtPoint.Value(ObservedValue own) -> {
                    yield switch (row.everyValueAt(place)) {
                        case WalkResult.CouldNotWalk<List<ObservedValue>> _ ->
                                new CameToNothing(ReadingGap.COULD_NOT_WALK);
                        case WalkResult.Reached(List<ObservedValue> every) ->
                                of(on.readAmong(own, every));
                    };
                }
                case ObservationAtPoint.WroteNothing _ -> new NothingWrittenThere();
                case ObservationAtPoint.BelongsToAnotherReading _ ->
                        new CameToNothing(ReadingGap.NO_VALUE);
            };
        };
    }

    /** The same over the values of a run, which a walk that was not taken has none of. */
    static WhatATermRead over(TermOrders on, WalkResult<List<ObservedValue>> answered) {
        return switch (answered) {
            case WalkResult.CouldNotWalk<List<ObservedValue>> _ ->
                    new CameToNothing(ReadingGap.COULD_NOT_WALK);
            case WalkResult.Reached(List<ObservedValue> values) -> of(on.readOver(values));
        };
    }

    /**
     * What {@code on} reads of a run computed of each element of the container {@code row} wrote.
     *
     * <p>Element by element, each read as the row with that element chosen, so the fields one
     * computation reads are the fields of one element. A field is looked at only where the
     * computation asks for it: a field the row wrote nothing at is a row that has no value for the
     * run where the computation needs it, and says nothing where the element's own choice does not
     * reach it. What stopped the first element that could not be read is what the row is told.
     */
    static WhatATermRead overElements(TermOrders on, RunSource.ComputedOccurrences computed,
                                      BorderQuantity.Observation row) {
        TermPath container = computed.elements().outermostContainer();
        if (!(row.eachElementOf(container)
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
                        case ObservationAtPoint.WroteNothing _ -> stop(new NothingWrittenThere());
                        case ObservationAtPoint.BelongsToAnotherReading _ ->
                                stop(new CameToNothing(ReadingGap.NO_VALUE));
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
            case NumericTerm.Reading.Missing(Incompleteness.Code code) ->
                    new CameToNothing(ReadingGap.of(code));
            case NumericTerm.Reading.NotNumber _ -> new NoNumberOfTheValue();
            case NumericTerm.Reading.NotWorkedOut(UnheldNumber why) ->
                    new CameToNothing(ReadingGap.of(why));
        };
    }
}
