package souther.compiler.generated;

import souther.compiler.coverage.NumberingIdentity;

/**
 * Whether the classes of an artifact record where a run goes, and under what numbering.
 *
 * <p>A number a probed class writes means a place only under the numbering that handed it out, and
 * the class has nothing to say about which numbering that was: what it holds is the number. So what
 * says it travels with the classes, because it is a fact about them — they were emitted with those
 * numbers in those calls, and nothing else about them says so.
 *
 * <p>Carried as the numbering's own value and not as the numbering. What crosses from a compile to
 * whatever runs a row is a thing two builds can be held against each other by; the capability to
 * issue an address belongs to a computation and stays in one.
 *
 * <p>Two arms because a build asks for the classes either way. Every evaluation runs against
 * counted classes and only a measurement asks for the probes, so most artifacts record nothing —
 * and a run against those is a run with no account of where it went, which is not the same as an
 * account of a run that went nowhere.
 */
public sealed interface ProbeImage {

    /** Classes with no probes in them: a run through these leaves nothing behind. */
    record Uninstrumented() implements ProbeImage {}

    /** Classes that record where a run goes, in the numbers {@code numbering} handed out. */
    record Instrumented(NumberingIdentity numbering) implements ProbeImage {

        public Instrumented {
            if (numbering == null) {
                throw new IllegalArgumentException(
                        "classes that record a run record it in somebody's numbers");
            }
        }
    }
}
