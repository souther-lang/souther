package souther.compiler.generated;

import souther.compiler.coverage.ArmReplacements;
import souther.compiler.coverage.NumberingIdentity;
import souther.compiler.coverage.WalkRewrites;

import java.util.Objects;

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

    /**
     * Classes that record where a run goes, in the numbers {@code numbering} handed out, that carry
     * at each of the arms {@code replacements} names the siblings a run can ask for in its place, and
     * at each of the walks {@code walks} names the switch a run asks to rewrite it by. The last two
     * travel with the first for the reason the first does: they are facts about what the classes
     * were emitted with, and nothing in them says them.
     */
    record Instrumented(NumberingIdentity numbering, ArmReplacements replacements,
                        WalkRewrites walks)
            implements ProbeImage {

        public Instrumented {
            if (numbering == null) {
                throw new IllegalArgumentException(
                        "classes that record a run record it in somebody's numbers");
            }
            Objects.requireNonNull(replacements,
                    "classes that record a run say which arms they carry siblings at, or none");
            Objects.requireNonNull(walks,
                    "classes that record a run say which walks they carry a switch at, or none");
        }
    }
}
