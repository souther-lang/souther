package souther.compiler.query;

/**
 * Whether a row went through one arm.
 *
 * <p>Two answers and no third. How far the reading behind them got is the {@link Measurement}
 * around this and never a state of it: {@code Complete(NoHit)} is no row goes through the arm and
 * every row was read, and {@code Partial(NoHit, ...)} is no row was seen to and something a row may
 * be sitting in was not.
 *
 * <p>Its own type beside {@link ItemAssessment.Coverage}, which answers the same two words about a
 * point of a line. What differs is what there is to say where nothing was asked: a line is read at a
 * position under a build that asked for no arms and under one no row names, and an arm has no such
 * states — a behavior whose arms nobody measured has no arm account at all. Sharing the type would
 * carry those reasons here as words nothing produces.
 */
public sealed interface ArmCoverage {

    /** A row this compilation observed went through the arm. Found is found: it went through it
     *  whatever became of the rows beside it. */
    record Hit() implements ArmCoverage {}

    /** No row that could be read went through the arm. */
    record NoHit() implements ArmCoverage {}

    /** Whether this is a row through the arm. Asked of the value, never of the measurement around
     *  it: what has no value has no answer here. */
    static boolean hit(ArmCoverage coverage) {
        return coverage instanceof Hit;
    }
}
