package souther.compiler.query;

import souther.compiler.check.Sig;

import java.util.Map;

/**
 * What a measure of one behavior has to work from at its boundary, or the fact that it has nothing.
 *
 * <p>The one place a missing signature becomes a measurement's business. {@code Bodies.Signatures}
 * is a partial map on purpose: a behavior whose declaration rests on a name nothing resolved has no
 * boundary to publish, so {@code SignatureBoundary} refuses to build one and the entry is never
 * made. That is an analysis saying what it could not work out, and it is right.
 *
 * <p>What is not an analysis's to say is what a report should do about it. Read straight, the
 * absence is a key a measure can skip — which is what both measures of a behavior's boundary did,
 * and what left a report crashing on one and going quiet on the other. Read here, it is a value the
 * measure carries: a measurement that was asked for, was started, and could not be finished.
 *
 * <p>So neither measure knows why there is no signature. Each asks this and answers for its own
 * measure: {@link Derived} is the boundary it measures, {@link NotDerived} is its own
 * {@code FailedToMeasure}. Which name went unresolved is reported where it was written, by the
 * module error the author acts on.
 */
public sealed interface BoundaryForMeasurement {

    /** The boundary a measure works from. */
    record Derived(Sig sig) implements BoundaryForMeasurement {

        public Derived {
            java.util.Objects.requireNonNull(sig, "a derived boundary is a signature");
        }
    }

    /**
     * There is none, so nothing that reads one could be measured.
     *
     * <p>A {@link FailureReason} as well as an arm, because it is both: the fact a measure holds
     * about its input, and the word every measure short of that input has no number for.
     */
    enum NotDerived implements BoundaryForMeasurement, FailureReason {
        BEHAVIOR_BOUNDARY_NOT_DERIVED
    }

    /** What the signatures of a module say about one of its behaviors. */
    static BoundaryForMeasurement of(Map<String, Sig> signatures, String behavior) {
        Sig sig = signatures.get(behavior);
        return sig == null ? NotDerived.BEHAVIOR_BOUNDARY_NOT_DERIVED : new Derived(sig);
    }

    /**
     * What a measure short of a boundary went without, as the fact that made it so.
     *
     * <p>Named by the behavior alone. Every measure of that behavior is short of the same one
     * thing, so the fact reaching a whole by two measures arrives once — which is what
     * {@link WeakeningSet} is for. A measure named beside it would make one cause into as many
     * facts as there are measures that read it.
     */
    static WeakeningSet wentWithout(String behavior) {
        return WeakeningSet.of(new Weakening.BoundaryNotDerived(behavior));
    }

    /** The measurement a measure short of a boundary comes to, whatever it measures. */
    static <T> Measurement<T> failed(String behavior) {
        return new Measurement.FailedToMeasure<>(NotDerived.BEHAVIOR_BOUNDARY_NOT_DERIVED,
                wentWithout(behavior));
    }

    /**
     * Whether this is a measure that went without one.
     *
     * <p>Asked here so that it is asked one way. Two readers spelling the same question — one
     * comparing the reason, one asking a measure of its own — are two places for the answer to
     * move apart the day another reason is added.
     */
    static boolean wasNotDerived(Measure<?> measure) {
        return measure.why() == NotDerived.BEHAVIOR_BOUNDARY_NOT_DERIVED;
    }
}
