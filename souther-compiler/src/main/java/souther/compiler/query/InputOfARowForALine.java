package souther.compiler.query;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.OrderedAffineBoundary;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The input of a row offered for one line, written as that line's reading names the positions.
 *
 * <p><b>The row's input, and not where anything was seen to stand.</b> A row offered for a line
 * comes from one of two places and they are known two ways: the search composed it, and the values
 * it asked for are what the row was built from; or another row already answers the line, and what
 * it holds there is what reading that row against the line came to. A value named for the second
 * would have nothing to say about the first — a row this compiler could not read back is a row a
 * person is handed all the same ({@link ItemAssessment.Attempt.Unverified}), and the input it was
 * composed at is the only thing there is to name for it.
 *
 * <p>The reading travels with the values because that is what they are written at. A line read in
 * two places is read at two sets of positions, and a place shown against the other reading names
 * positions the row says nothing about.
 *
 * @param reading the line as the reading this row belongs to met it
 * @param at      the row's positions, on that reading
 */
public record InputOfARowForALine(Border reading, Map<NumericTerm, Place> at) {

    public InputOfARowForALine {
        at = Collections.unmodifiableMap(new LinkedHashMap<>(at));
        if (reading == null || at.isEmpty()) {
            throw new IllegalArgumentException(
                    "a row's input on a line is the positions that reading names: " + reading);
        }
    }

    /**
     * The input as an author would write the positions, or null where this reading's quantity names
     * a position the row holds no number at.
     *
     * <p>Written by the line rather than by whoever shows it, so that the one place a report names
     * and the row a person is handed are spelled out of the same reading.
     */
    public String said() {
        return OrderedAffineBoundary.saidAt(reading.cut().of(), at);
    }
}
