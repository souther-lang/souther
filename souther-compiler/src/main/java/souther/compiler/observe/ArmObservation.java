package souther.compiler.observe;

/**
 * Whether a run records which arm of each body it went through.
 *
 * <p>Not how much of it is measured. Every evaluation is counted whatever this says — what holds a
 * row to a budget it cannot exceed is the counting itself, so a run recording nothing is still a
 * counted one, and reading either answer as "not measured" gets the emitted bodies wrong. What this
 * decides is the one thing beside the counting: whether the bodies carry a point at each arm, so
 * that a measurement can read which of them the rows reached.
 *
 * <p>Asked of the run and not of the report. Two adequacy levels wanting the same thing recorded
 * are one evaluation, and a wider report over what was already run does not run the rows again.
 */
public enum ArmObservation {

    /** Do not record them. What a run asks for when nobody is reading which arms it took. */
    OMIT,

    /** Record which arm of each of the module's bodies the rows took. */
    RECORD
}
