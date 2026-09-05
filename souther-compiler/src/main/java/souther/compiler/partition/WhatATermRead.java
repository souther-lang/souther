package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.numeric.Place;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;

import java.util.List;

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
    record Number(Place value) implements WhatATermRead { }

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
    record CameToNothing(ReadingGap why) implements WhatATermRead { }

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

    /** The same over the values of a run, which a walk that was not taken has none of. */
    static WhatATermRead over(TermOrders on, WalkResult<List<ObservedValue>> answered) {
        return switch (answered) {
            case WalkResult.CouldNotWalk<List<ObservedValue>> _ ->
                    new CameToNothing(ReadingGap.COULD_NOT_WALK);
            case WalkResult.Reached(List<ObservedValue> values) -> of(on.readOver(values));
        };
    }

    /** What a term's own reading of a value comes to here. */
    private static WhatATermRead of(NumericTerm.Reading read) {
        return switch (read) {
            case NumericTerm.Reading.Number(Place value) -> new Number(value);
            case NumericTerm.Reading.Missing(Incompleteness.Code code) ->
                    new CameToNothing(ReadingGap.of(code));
            case NumericTerm.Reading.NotNumber _ -> new NoNumberOfTheValue();
        };
    }
}
