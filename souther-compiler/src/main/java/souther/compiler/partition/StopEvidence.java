package souther.compiler.partition;

import souther.compiler.inputs.EveryRunStops;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.meaning.Proposition;

import java.util.List;
import java.util.Objects;
import java.util.function.Supplier;

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
 * not, nothing is said of where a run stops. Where the owner of what may end a run says it may
 * end one there, the report says the comparison is not read to the end ({@link GuardThresholds}).
 *
 * <p>What is not among {@code operations} may still be said: a reading that kept what a run
 * works out on each arm of a choice, or on each way of a total, says the stops there and not
 * here, and so does one that told a part beside the rows. {@code everyStopSaid} is that every
 * stop a run getting here may meet is among these operations or among what the same reading
 * says on its arms and ways ({@link ComparisonReadings.Reading#whatARunWorksOut}); not so where
 * a stop is left untold, or left to an owner that says it nowhere among them.
 *
 * @param operations    every operation of whole numbers the run works out, in the order it does,
 *                      and whether that is every one and is worked out on every run getting there
 * @param everyStopSaid whether every stop a run getting here may meet is said, here or on the
 *                      arms and ways the same reading says what is worked out on
 */
record StopEvidence(UndividedByARelation.Working operations, boolean everyStopSaid) {

    StopEvidence {
        Objects.requireNonNull(operations, "what a run works out, or that it is not known");
    }

    /**
     * What a run taking an arm of a choice works out there, and where the arm is taken: a run
     * that takes another works none of it out, so none of it is said of every run getting to the
     * comparison.
     *
     * <p>Where the arm is taken is worked out the first time a reader asks: most arms are asked
     * only what a run works out, and an arm of many ways would otherwise join the conditions of
     * each for nobody.
     */
    static final class OnAnArm {

        private final Supplier<Proposition> reached;
        private final StopEvidence stops;

        /** An arm taken where {@code reached} holds, a run taking which works out {@code stops}. */
        OnAnArm(Proposition reached, StopEvidence stops) {
            this(supplied(reached), stops);
        }

        private OnAnArm(Supplier<Proposition> reached, StopEvidence stops) {
            this.reached = reached;
            this.stops = Objects.requireNonNull(stops,
                    "and a run taking it works something out");
        }

        /** The same, where the arm is taken worked out by {@code reached} when it is asked. */
        static OnAnArm takenWhere(Supplier<Proposition> reached, StopEvidence stops) {
            return new OnAnArm(new Pullback.Once<>(() -> Objects.requireNonNull(reached.get(),
                    "an arm is taken somewhere, if only nowhere")), stops);
        }

        private static Supplier<Proposition> supplied(Proposition reached) {
            Objects.requireNonNull(reached, "an arm is taken somewhere, if only nowhere");
            return () -> reached;
        }

        /** Where the arm is taken. */
        Proposition reached() {
            return reached.get();
        }

        /** What a run taking it works out there. */
        StopEvidence stops() {
            return stops;
        }
    }

    /** What a reading that leaves nothing to a witness says a run works out: what a row of its
     *  lines gets past. */
    static StopEvidence ofWhatIsToldOf(UndividedByARelation.Working working) {
        return new StopEvidence(working, working.exact() && !working.aStopUntold());
    }

    /** Whether every operation that can stop a run is among {@link #operations}: not where a
     *  stop is left untold ({@link UndividedByARelation.Working#aStopUntold}). */
    boolean exact() {
        return operations.exact() && !operations.aStopUntold();
    }

    /** Whether no operation is told ({@link UndividedByARelation#tellsNoOperation}). Nothing is
     *  said of whether a run stops: no reading made, one that met something it told nothing for,
     *  and one that showed no operation stops all tell no operation. Not said where a stop is
     *  left untold. */
    boolean tellsNoOperation() {
        return !operations.aStopUntold() && UndividedByARelation.tellsNoOperation(operations);
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
