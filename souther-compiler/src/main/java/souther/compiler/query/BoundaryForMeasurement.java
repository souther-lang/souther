package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.Sig;
import souther.compiler.inputs.InputDomain;
import souther.compiler.observe.MeasureReason;

import java.util.Map;
import java.util.Objects;

/**
 * What a measure of one behavior has to work from at its boundary, or which part of it is missing.
 *
 * <p>A signature, and where what the behavior takes is read. The signature says what it takes and
 * answers with; where its input is read is {@link InputForMeasurement} — here, as a reading whose
 * positions and numbers a measure goes on to ask about, or at its stages for a {@code >->}
 * composition. So a boundary that was worked out always has a signature, and holds a reading only
 * where the behavior has an input of its own.
 *
 * <p>They go missing for different reasons, which is why {@link NotDerived} has two: a declaration
 * resting on a name nothing resolved has no signature, and a module holding a type nobody could
 * name has no reading of what any of its behaviors take. A behavior can have the first and not the
 * second.
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
     * The boundary a measure works from: what the behavior declares, and where what it takes is
     * read.
     *
     * <p>The second because of what happened without it. Handed the signature alone, a reader that
     * needed the reading took it from a map that may not hold one and read the absence as an input
     * with no positions — which measures as an input the model divides nowhere. Here a measure is
     * told where what the behavior takes is read, and a behavior whose reading could not be made is
     * not one of these at all.
     *
     * @param input where what this behavior takes is read ({@link InputForMeasurement}), which is
     *              here for a declared behavior and at its stages for a composition. A boundary
     *              this compilation could not work out is not one of these
     */
    record Derived(Sig sig, InputForMeasurement input) implements BoundaryForMeasurement {

        public Derived {
            Objects.requireNonNull(sig, "a derived boundary is a signature");
            Objects.requireNonNull(input, "a derived boundary says where its input is read");
        }
    }

    /**
     * The signature, or a reading this behavior was owed, is missing — so nothing that reads the
     * boundary could be measured.
     *
     * <p>A {@link FailureReason} as well as an arm, because it is both: the fact a measure holds
     * about its boundary, and the word every measure short of it has no number for.
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

        /** Both are read off one behavior's own declaration and its own input, so two behaviors of
         *  one run can say different ones. */
        @Override
        public MeasureReason.About about() {
            return MeasureReason.About.THE_BEHAVIOR;
        }

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
     * stage takes and is read there, which is what {@link InputForMeasurement.AtStages} says — told
     * apart by the name alone, every composition in the module reads as a behavior whose input
     * nobody could read.
     *
     * <p><b>The one place a behavior is put in one of these states.</b> A measure that worked it out
     * again from the signatures, the kind of the declaration and a lookup that may miss would be
     * deciding a second time what a missing entry means, and the two decisions moved apart: of the
     * two readers of one reachability walk, one skipped a behavior whose input was not read and the
     * other measured it against an input with no positions.
     *
     * <p><b>Three steps, in this order.</b> A signature is asked for first, and without one there is
     * no boundary whatever the behavior is. With one in hand the declaration says whether a reading
     * of an input of its own is owed at all — a composition's is its first stage's — and only where
     * one is owed is its presence asked about. Taken in the other order, a module whose reading
     * could not be made would report every composition in it as a behavior whose input nobody could
     * read.
     *
     * <p>Which is not the question of whether a measure applies to this behavior. That one is the
     * declaration's, asked by each measure that has a subject to choose; what is answered here is
     * what this compilation worked out.
     */
    static BoundaryForMeasurement of(Map<String, Sig> signatures,
                                     Map<String, InputDomain> read,
                                     Hir.BehaviorDef behavior) {
        Sig sig = signatures.get(behavior.name());
        if (sig == null) {
            return NotDerived.BEHAVIOR_BOUNDARY_NOT_DERIVED;
        }
        if (!(behavior instanceof Hir.SpecBehavior spec)) {
            return new Derived(sig, InputForMeasurement.AtStages.INSTANCE);
        }
        InputDomain inputs = read == null ? null : read.get(spec.name());
        return inputs == null ? NotDerived.BEHAVIOR_INPUT_NOT_READ
                : new Derived(sig, new InputForMeasurement.Local(spec, inputs));
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
