package souther.compiler.codegen;

import java.util.Objects;

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
 * <p><b>Whether the arms are numbered and not which numbering they get.</b> A plan is made from
 * bodies, by identity, and the only bodies it can be made from are the ones being emitted. Carried
 * here it would be a second answer to a question the bodies already answer, and a caller could hand
 * over a plan of one set of bodies with another set to emit — a pair the emitter can only refuse
 * once it is already walking. So the plan is made where the bodies are ({@link Backend}), and what a
 * caller says is which of the two things it wants.
 *
 * <p>{@link #NONE} is what ships: bytecode with no reference to either.
 */
public record Instrumentation(Coverage coverage, boolean counting) {

    /** Whose arms a generation numbers. */
    public enum Coverage {

        /** Nobody's. The bytecode holds no probe and a run through it leaves no account. */
        NONE,

        /** The bodies this generation is emitting, which are the only ones it can number. */
        THE_BODIES_BEING_EMITTED
    }

    /** What a generation whose classes are written out gets. */
    public static final Instrumentation NONE = new Instrumentation(Coverage.NONE, false);

    /** What every evaluation runs against: counted, and measuring nothing. */
    public static final Instrumentation COUNTING = new Instrumentation(Coverage.NONE, true);

    public Instrumentation {
        Objects.requireNonNull(coverage, "a generation says whose arms it numbers, Coverage.NONE"
                + " where it numbers none");
    }

    /** The same, also numbering the arms of the bodies being emitted — for the one module a
     *  measurement is about. */
    public Instrumentation measuring() {
        return new Instrumentation(Coverage.THE_BODIES_BEING_EMITTED, counting);
    }

    /** Whether the arms of the bodies being emitted are numbered. */
    public boolean measuresCoverage() {
        return coverage == Coverage.THE_BODIES_BEING_EMITTED;
    }
}
