package souther.compiler.observe;

/**
 * Whether a source's rows were run here, and what came of it if they were.
 *
 * <p>Two and not one. What running the rows turned up and the rows not having been run are
 * different answers, and {@link Observations} says the first with the same empty lists it would say
 * "nothing was wrong" with. A reader given only observations has to work out from their emptiness
 * which of the two it got, and the two mean opposite things to a measure: one is a model with
 * nothing to report and the other is a measure that was never made.
 *
 * <p>Nothing says why nothing ran. Whether the classes could not be emitted, could not be linked or
 * could not be instrumented are the machine's account of its own trouble, and what the caller does
 * about it turns on what the caller asked for rather than on which of them it was.
 */
public sealed interface RowRun {

    /** The rows ran, and this is what was observed. */
    record Ran(Observations observed) implements RowRun {

        public Ran {
            if (observed == null) {
                throw new IllegalArgumentException("a run that happened was observed");
            }
        }
    }

    /** Nothing ran, so nothing is known about these rows from here. */
    record NotRunHere() implements RowRun {}
}
