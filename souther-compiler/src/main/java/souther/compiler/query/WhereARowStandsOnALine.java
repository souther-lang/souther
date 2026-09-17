package souther.compiler.query;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.OrderedAffineBoundary;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Where a row a person is handed stands on one line, as that line's own reading names the positions.
 *
 * <p><b>The offered row's place, and not the composed row's.</b> A row is composed for one thing and
 * a run offers the rows whose going would cost it something ({@link Settlements#keeping}), so the
 * row that ends up in front of a person for a line need not be the one composed for it: another row
 * that tells the two lines apart answers the line as well, and the one composed for it then goes.
 * A place read off the search is a place from before that was decided.
 *
 * <p>The reading travels with the values because that is what they are written at. A line read in
 * two places is read at two sets of positions, and a place shown against the other reading names
 * positions the row says nothing about.
 *
 * @param reading the line as the reading this row was read at met it
 * @param at      where the row's positions stand on that reading
 */
public record WhereARowStandsOnALine(Border reading, Map<NumericTerm, Place> at) {

    public WhereARowStandsOnALine {
        at = Collections.unmodifiableMap(new LinkedHashMap<>(at));
        if (reading == null || at.isEmpty()) {
            throw new IllegalArgumentException(
                    "a row stands on a line at the positions that reading names: " + reading);
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
