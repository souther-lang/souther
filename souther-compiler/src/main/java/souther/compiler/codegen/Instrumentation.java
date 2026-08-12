package souther.compiler.codegen;

import souther.compiler.coverage.CoverageSites;

/**
 * What a generation adds to the code beyond what the code says, and why.
 *
 * <p>Two things, kept apart because they are asked for by different callers about different scopes.
 * {@code coverage} numbers the arms of one module's bodies and is asked for by a measurement, so it is
 * about the module being measured and no other. {@code counting} holds the code to a budget and is
 * what every evaluation runs under, so it goes on every module a row can reach. A generation that
 * confused them would either measure arms in modules whose report has no way to read the numbers, or
 * let a row spend an unbounded amount of time as soon as it stepped into an import.
 *
 * <p>They are also planned differently. An arm is a node of a body the plan was made from, looked up
 * by identity; a counted point is any loop the emitter emits, which includes loops in a decoder that
 * no body has a node for. So there is nothing for the two to share but this record.
 *
 * <p>{@link #NONE} is what ships: bytecode with no reference to either.
 */
public record Instrumentation(CoverageSites.Plan coverage, boolean counting) {

    /** What a generation whose classes are written out gets. */
    public static final Instrumentation NONE = new Instrumentation(CoverageSites.Plan.NONE, false);

    /** What every evaluation runs against: counted, and measuring nothing. */
    public static final Instrumentation COUNTING =
            new Instrumentation(CoverageSites.Plan.NONE, true);

    public Instrumentation {
        if (coverage == null) {
            throw new IllegalArgumentException("a coverage plan is required; use Plan.NONE for none");
        }
    }

    /** The same, also numbering {@code plan}'s arms — for the one module a measurement is about. */
    public Instrumentation measuring(CoverageSites.Plan plan) {
        return new Instrumentation(plan, counting);
    }
}
