package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * What one quantity's positions hold at one row: a number for each of them, or why there is none.
 *
 * <p>The values before anything is weighed. {@link BorderQuantity#standsAt} asks what a row comes to
 * against the line the model drew and answers yes or no; this hands back the numbers the line was
 * drawn over, so that a caller can hold the row against a line the model did not draw. A caller
 * given the yes or no could only ever ask about the one line.
 *
 * <p>The same three answers a quantity gives about standing somewhere, and for the same reasons. A
 * row that wrote nothing where a position is has no value for the quantity, which is the row's own
 * answer; a reading this compiler could not make is its own shortfall and carries what stopped it;
 * and neither is a number.
 */
public sealed interface ValuesAtARow {

    /** The number each of the quantity's positions holds. */
    record Read(Map<NumericTerm, Place> values) implements ValuesAtARow {

        public Read {
            if (values == null || values.isEmpty()) {
                throw new IllegalArgumentException(
                        "a row read at a quantity holds a number at each of its positions");
            }
            values = Collections.unmodifiableMap(new LinkedHashMap<>(values));
        }
    }

    /** The row was read and this quantity has no value at it. */
    record NoneHere() implements ValuesAtARow {}

    /**
     * There was nothing to read, and this is every reason there was not.
     *
     * <p>Every one of them, the way a quantity collects them over its terms: a quantity read over
     * several positions comes to nothing for whatever stopped any of them, and naming one would be
     * picking which of them a reader is told about.
     */
    record CouldNotTell(Set<ReadingGap> why) implements ValuesAtARow {

        public CouldNotTell {
            if (why == null || why.isEmpty()) {
                throw new IllegalArgumentException(
                        "a reading nothing could be made of says what stopped it");
            }
            why = Collections.unmodifiableSet(new LinkedHashSet<>(why));
        }
    }

    ValuesAtARow NONE_HERE = new NoneHere();
}
