package souther.compiler.partition;

import souther.compiler.inputs.EveryRunStops;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.SearchRegion;

import java.util.List;
import java.util.Objects;

/**
 * What a run getting to a comparison works out on the way to its answer, every operation of it,
 * for saying where a run stops — and not what a row of a line the comparison draws is asked to
 * get past.
 *
 * <p>The two are read off one reading of the comparison's arithmetic, and are not one answer. A
 * line on a remainder of {@code a + x} is drawn where some {@code x} takes the sum through every
 * remainder within its type, so the sum is the witness's to get past and is no operation a row of
 * the line is asked to ({@link UndividedByARelation.Working}). A run with {@code a + x} past its
 * type stops in it all the same, and that is what this says. Where a reading leaves nothing to a
 * witness the two hold the same operations.
 *
 * <p>Not having read an operation is not having shown none stops a run: {@code operations} tells
 * every one only where it says so ({@link UndividedByARelation.Working#exact}), and where it does
 * not, nothing is said of where a run stops.
 *
 * @param operations every operation of whole numbers the run works out, in the order it does, and
 *                   whether that is every one and is worked out on every run getting there
 */
record StopEvidence(UndividedByARelation.Working operations) {

    StopEvidence {
        Objects.requireNonNull(operations, "what a run works out, or that it is not known");
    }

    /** What a reading that leaves nothing to a witness says a run works out: what a row of its
     *  lines gets past. */
    static StopEvidence ofWhatIsToldOf(UndividedByARelation.Working working) {
        return new StopEvidence(working);
    }

    /** Whether every operation that can stop a run is among {@link #operations}. */
    boolean exact() {
        return operations.exact();
    }

    /**
     * Where every run getting here stops in what it works out, over {@code regions}, where it may
     * also work out {@code alsoWorkedOut} first ({@link UndividedByARelation#everyRunStopsIn}).
     */
    List<EveryRunStops> everyRunStopsIn(InputReading read, List<SearchRegion> regions,
                                        List<UndividedByARelation.IntOperation> alsoWorkedOut) {
        return UndividedByARelation.everyRunStopsIn(operations, read, regions, alsoWorkedOut);
    }
}
