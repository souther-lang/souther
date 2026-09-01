package souther.compiler.query;

import souther.compiler.check.Sig;
import souther.compiler.inputs.InputDomain;

import java.util.Map;

/**
 * What a measure of one behavior has to work from at its boundary, or which part of it is missing.
 *
 * <p>Two things and not one. A signature says what the behavior takes and answers with, and a
 * reading of the input says where its positions are and what the rules leave the numbers at them.
 * A measure that reads the boundary needs both, and they go missing for different reasons: a
 * declaration resting on a name nothing resolved has no signature, and a module holding a type
 * nobody could name has no reading of what any of its behaviors take. A behavior can have the
 * first and not the second.
 *
 * <p>What is not an analysis's to say is what a report should do about either. Read straight, the
 * absence is a key a measure can skip — which is what both measures of a behavior's boundary did,
 * and what left a report crashing on one and going quiet on the other. Read here, it is a value the
 * measure carries: a measurement that was asked for, was started, and could not be finished.
 *
 * <p>So no measure works out why it has nothing to work from. Each asks this and answers for its
 * own measure: {@link Derived} is the boundary it measures, {@link NotDerived} is its own
 * {@code FailedToMeasure} and says which half was missing. Which name went unresolved is reported
 * where it was written, by the module error the author acts on.
 */
public sealed interface BoundaryForMeasurement {

    /**
     * The boundary a measure works from: what the behavior declares, and the input as it was read.
     *
     * <p>Both, because a measure that reads one reads the other. Handed the signature alone, a
     * reader that needed the reading took it from a map that may not hold one and read the absence
     * as an input with no positions — which measures as an input the model divides nowhere.
     *
     * @param inputs {@link InputDomain#NONE} for a behavior with no input of its own, which is a
     *               {@code >->} composition: what it takes is its first stage's and is read there
     */
    record Derived(Sig sig, InputDomain inputs) implements BoundaryForMeasurement {

        public Derived {
            java.util.Objects.requireNonNull(sig, "a derived boundary is a signature");
            java.util.Objects.requireNonNull(inputs, "a derived boundary is an input that was read");
        }
    }

    /**
     * One of the two is missing, so nothing that reads the boundary could be measured.
     *
     * <p>A {@link FailureReason} as well as an arm, because it is both: the fact a measure holds
     * about its input, and the word every measure short of that input has no number for.
     */
    enum NotDerived implements BoundaryForMeasurement, FailureReason {

        /** The declaration rests on a name nothing resolved, so there is no signature to read. */
        BEHAVIOR_BOUNDARY_NOT_DERIVED,

        /**
         * The signature is in hand and the input was not read.
         *
         * <p>Its own word beside the one above, because it sends a reader somewhere else. A
         * behavior whose boundary was not derived has an unresolved name in its own declaration;
         * this one does not — what is unread is the input, which a hole anywhere in the module
         * refuses the reading of.
         */
        BEHAVIOR_INPUT_NOT_READ;

        /**
         * What a measure short of this went without, as the fact that made it so.
         *
         * <p>Named by the behavior alone. Every measure of that behavior is short of the same one
         * thing, so the fact reaching a whole by two measures arrives once — which is what
         * {@link WeakeningSet} is for. A measure named beside it would make one cause into as many
         * facts as there are measures that read it.
         */
        public WeakeningSet wentWithout(String behavior) {
            return WeakeningSet.of(switch (this) {
                case BEHAVIOR_BOUNDARY_NOT_DERIVED -> new Weakening.BoundaryNotDerived(behavior);
                case BEHAVIOR_INPUT_NOT_READ -> new Weakening.InputNotRead(behavior);
            });
        }

        /**
         * The measurement a measure short of this comes to, whatever it measures.
         *
         * <p>Asked of the reason rather than handed one, so that which fact a reader is told goes
         * with which word the measure carries. Chosen apart, a measure could say it stopped at one
         * of the two and name the other as what it went without.
         */
        public <T> Measurement<T> failed(String behavior) {
            return new Measurement.FailedToMeasure<>(this, wentWithout(behavior));
        }
    }

    /**
     * What a module's signatures and its reading of what its behaviors take say about one of them.
     *
     * <p>Asked of the declaration rather than of the name, because only a declaration says whether
     * this behavior has an input of its own to read. A {@code >->} composition takes what its first
     * stage takes and is read there, so having no reading here is what it is rather than a reading
     * that was refused — and told apart by the name alone, every composition in the module reads as
     * a behavior whose input nobody could read.
     */
    static BoundaryForMeasurement of(Map<String, Sig> signatures,
                                     Map<String, InputDomain> read,
                                     souther.compiler.ast.Hir.BehaviorDef behavior) {
        Sig sig = signatures.get(behavior.name());
        if (sig == null) {
            return NotDerived.BEHAVIOR_BOUNDARY_NOT_DERIVED;
        }
        if (!(behavior instanceof souther.compiler.ast.Hir.SpecBehavior)) {
            return new Derived(sig, InputDomain.NONE);   // its input is its first stage's
        }
        InputDomain inputs = read == null ? null : read.get(behavior.name());
        return inputs == null ? NotDerived.BEHAVIOR_INPUT_NOT_READ : new Derived(sig, inputs);
    }

    /**
     * Whether this is a measure that went without something its boundary is made of.
     *
     * <p>Asked here so that it is asked one way. Two readers spelling the same question — one
     * comparing the reason, one asking a measure of its own — are two places for the answer to
     * move apart when another reason is added.
     */
    static boolean wasNotDerived(Measure<?> measure) {
        return measure.why() instanceof NotDerived;
    }
}
