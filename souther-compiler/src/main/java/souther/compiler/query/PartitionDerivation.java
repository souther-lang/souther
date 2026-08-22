package souther.compiler.query;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.partition.MeasureClosure;

import java.util.List;

/**
 * What the partition measure came to over one behavior: the positions it is measured at, or — where
 * there are none — which nothing there is.
 *
 * <p>One value and not a list beside a status. The list used to answer both questions and could
 * answer neither: an empty one is what a behavior whose model divides nothing has, what a behavior
 * whose positions could not be read has, and what a {@code >->} composition has, and a reader
 * counting entries called all three measured. Split into a list and a status held next to it, the
 * two could still be built out of step — {@code axes} full beside an answer saying nothing was
 * found — and the invariant would be a constructor check over a state the type still let anybody
 * write.
 *
 * <p>So the evidence lives inside the arm that has any, and the arms that have none carry no list to
 * read. {@code []} never leaves this type.
 *
 * <p><b>{@link Absent} is a conclusion and costs a proof to say.</b> It takes the closure of this
 * measure's own reading, which only {@code souther.compiler.partition} can produce — the same
 * arrangement {@code UndividedPosition.Why.Absent} is under. The sentence "the model divides
 * nothing anywhere and no row would change that" is the one that must not be cheap to write, since
 * it is what takes a behavior out of the verdict.
 *
 * <p><b>Which reading is asked is this measure's own.</b> Not "every reader ran to the end": which
 * readers there are is a fact about this compiler, and a completeness written off them moves when
 * one is added. The closure is over the questions the model raised that this measure answers
 * ({@code CoverageObligation.answeredBy}), so a rule whose line nothing could read leaves the border
 * measure short and this one whole.
 */
public sealed interface PartitionDerivation {

    /** How much of the measure was made, which is what every reader of a measure asks first. */
    MeasurementStatus status();

    /** Why there is no number, or null where there is one. */
    Reason reason();

    /** The positions this behavior is measured at, empty where the measure has none to show. */
    List<PartitionEvidence.AxisCoverage> at();

    /**
     * Why the partition measure has no number.
     *
     * <p>One constant per arm that has none, and never one shared between two. Which kind of
     * no-number each is, is the reason's own answer.
     */
    enum Reason implements souther.compiler.observe.MeasureReason {

        /**
         * The reading of what this measure answers did not run out, so what it did not find is not
         * known not to be there. A rule about a position's values that nothing took in, a position
         * whose rules were never enumerated, a position dropped past the axis limit.
         *
         * <p>What {@code NO_AXIS_DERIVED} said of every empty answer, now said only where it is
         * true. Its own javadoc stated the problem it had: whether the model draws no line anywhere
         * or the reading stopped short of one was not something it could tell.
         */
        THE_READING_DID_NOT_RUN_OUT(MeasurementStatus.NOT_MEASURED),

        /**
         * Every question this measure answers was answered, and the model divides no position of
         * this behavior into classes.
         *
         * <p>Nothing here for the measure to be about. A plain {@code String}, an {@code Int} no
         * rule cuts, a {@code List} whose elements were reached and have no rule about them: no row
         * an author writes puts a class there, and only editing the model would. Counted in the
         * verdict, one such behavior held every model it appears in open for a measurement that was
         * never anybody's to make.
         */
        NOTHING_IS_DIVIDED(MeasurementStatus.NOT_APPLICABLE),

        /** This behavior has no positions for the measure to be about — a {@code >->} composition,
         *  which is measured at its stages. */
        NO_SUBJECT(MeasurementStatus.NOT_APPLICABLE);

        private final MeasurementStatus status;

        Reason(MeasurementStatus status) {
            this.status = status;
        }

        @Override
        public MeasurementStatus status() {
            return status;
        }
    }

    /** The measure was made in full: every question it answers was answered, and these are the
     *  positions it found. */
    record Complete(List<PartitionEvidence.AxisCoverage> at) implements PartitionDerivation {

        public Complete {
            at = List.copyOf(at);
            if (at.isEmpty()) {
                // Not recovered to an absence. A measure that says it found positions and shows
                // none is two accounts of one reading disagreeing, and answering either way would
                // report one of them as the model.
                throw new IllegalStateException(
                        "a complete partition with no position is a measure disagreeing with itself");
            }
        }

        @Override
        public MeasurementStatus status() {
            return MeasurementStatus.COMPLETE;
        }

        @Override
        public Reason reason() {
            return null;
        }
    }

    /**
     * Positions were found, and the reading this measure depends on did not run out.
     *
     * <p>The other half of what {@link Absent} and {@link Unresolved} are about. An empty answer
     * from a reading that stopped is not a measurement, and neither is a full one: a rule nothing
     * took in may divide a position that came back with two classes, so the classes are what was
     * read and not what the model states. Reported as complete, a build was told a model was
     * covered on the strength of the rules this compiler happened to manage.
     */
    record Partial(List<PartitionEvidence.AxisCoverage> at) implements PartitionDerivation {

        public Partial {
            at = List.copyOf(at);
            if (at.isEmpty()) {
                throw new IllegalStateException(
                        "a partial partition with no position is `Unresolved`, which says so");
            }
        }

        @Override
        public MeasurementStatus status() {
            return MeasurementStatus.PARTIAL;
        }

        @Override
        public Reason reason() {
            return null;
        }
    }

    /**
     * The reading ran out and the model divides nothing.
     *
     * <p>The argument is the proof, as it is for a position. A caller able to write this without
     * one could say the model divides no position anywhere without having asked, and that sentence
     * is what takes a behavior out of the verdict.
     */
    record Absent(MeasureClosure.OfThePartition.Closed proven) implements PartitionDerivation {

        public Absent {
            java.util.Objects.requireNonNull(proven, "an absence is what a closed reading came to");
        }

        @Override
        public MeasurementStatus status() {
            return Reason.NOTHING_IS_DIVIDED.status();
        }

        @Override
        public Reason reason() {
            return Reason.NOTHING_IS_DIVIDED;
        }

        @Override
        public List<PartitionEvidence.AxisCoverage> at() {
            return List.of();
        }
    }

    /** No position came back and the reading did not run out, so nothing is established either
     *  way. */
    record Unresolved() implements PartitionDerivation {

        @Override
        public MeasurementStatus status() {
            return Reason.THE_READING_DID_NOT_RUN_OUT.status();
        }

        @Override
        public Reason reason() {
            return Reason.THE_READING_DID_NOT_RUN_OUT;
        }

        @Override
        public List<PartitionEvidence.AxisCoverage> at() {
            return List.of();
        }
    }

    /** This behavior has no positions of its own for the measure to be about. */
    record NoSubject() implements PartitionDerivation {

        @Override
        public MeasurementStatus status() {
            return Reason.NO_SUBJECT.status();
        }

        @Override
        public Reason reason() {
            return Reason.NO_SUBJECT;
        }

        @Override
        public List<PartitionEvidence.AxisCoverage> at() {
            return List.of();
        }
    }

    /**
     * What the measure came to, from what it found and whether its reading ran out.
     *
     * <p>The one place the four are chosen between, so that no caller pairs an answer with evidence
     * it does not go with. Nothing is decided from the shape of {@code at} alone: an empty answer is
     * an absence or an unresolved reading depending on the closure, and a full one is complete or
     * partial by the same fact.
     */
    static PartitionDerivation of(List<PartitionEvidence.AxisCoverage> at,
                                  MeasureClosure.OfThePartition closure) {
        if (closure instanceof MeasureClosure.OfThePartition.Closed closed) {
            return at.isEmpty() ? new Absent(closed) : new Complete(at);
        }
        return at.isEmpty() ? new Unresolved() : new Partial(at);
    }
}
