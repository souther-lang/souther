package souther.compiler.query;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.partition.MeasureClosure;

import java.util.List;

/**
 * What the border measure came to over one behavior: the lines its rules drew, or — where there are
 * none — which nothing there is.
 *
 * <p>The same five answers as {@link PartitionDerivation}, and a separate type. The two measures are
 * short of different things and reach empty for different reasons — an enumeration divides and has
 * no line, an invariant's bound has a line and divides nothing — so a behavior is routinely one
 * answer at one and another at the other. Shared, each would be reported on the strength of whatever
 * stopped its neighbour.
 *
 * <p><b>{@link Absent} costs a proof.</b> #521 is what that protects. A boundary measure that
 * derived nothing may have been reading a model whose bounds sit where this could not get to, and
 * calling it measured says the rows carrying a model's whole risk earned nothing. That case cannot
 * reach an absence here because a reading that stopped produces no {@code Closed} — the protection
 * is the shape of the type and not a condition anybody has to remember to write.
 *
 * <p>And {@link Partial} is #521's other half, which was missing while the question was only about
 * empty answers. A behavior one of whose rules drew a line and another of whose lines nothing could
 * read has borders to show and a measure that was not made in full; reported complete, a build was
 * held to what this compiler managed rather than to what the model states.
 */
public sealed interface BoundaryDerivation {

    /** How much of the measure was made. */
    MeasurementStatus status();

    /** Why there is no number, or null where there is one. */
    Reason reason();

    /** The lines this behavior is measured at, empty where the measure has none to show. */
    List<BorderAssessment> at();

    /** Why the border measure has no number. */
    enum Reason implements souther.compiler.observe.MeasureReason {

        /**
         * The reading of what this measure answers did not run out. A rule that places an end and
         * could not be turned into a line, a position whose rules were never reached, a position
         * dropped past the axis limit.
         *
         * <p>What {@code NO_LINES_DERIVED} said of every empty answer. #521 made it
         * {@code NOT_MEASURED} because nothing could tell a model whose bounds sit one type away
         * from a model with no bound at all; the closure tells them apart, and this is what is left
         * of the first.
         */
        THE_READING_DID_NOT_RUN_OUT(MeasurementStatus.NOT_MEASURED),

        /**
         * Every question this measure answers was answered, and no rule of the model draws a line
         * anywhere on this behavior's positions.
         *
         * <p>A row cannot make a line. What draws one is a rule — an invariant's bound, a
         * {@code guard}'s comparison — so a behavior over an enumeration nothing bounds has no line
         * for a row to be at and no row that could put one there. That is nothing for the measure to
         * be about, and counting it held the module's verdict open for as long as the behavior
         * existed.
         */
        NO_RULE_DRAWS_A_LINE(MeasurementStatus.NOT_APPLICABLE),

        /** This behavior has no positions for a line to be drawn on — a {@code >->} composition,
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

    /** Every question this measure answers was answered, and these are the lines it found. */
    record Complete(List<BorderAssessment> at) implements BoundaryDerivation {

        public Complete {
            at = List.copyOf(at);
            if (at.isEmpty()) {
                throw new IllegalStateException(
                        "a complete border measure with no line is a measure disagreeing with itself");
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

    /** Lines were drawn, and something this measure answers for went unanswered. */
    record Partial(List<BorderAssessment> at) implements BoundaryDerivation {

        public Partial {
            at = List.copyOf(at);
            if (at.isEmpty()) {
                throw new IllegalStateException(
                        "a partial border measure with no line is `Unresolved`, which says so");
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

    /** The reading ran out and no rule draws a line. The argument is the proof. */
    record Absent(MeasureClosure.OfTheBorder.Closed proven) implements BoundaryDerivation {

        public Absent {
            java.util.Objects.requireNonNull(proven, "an absence is what a closed reading came to");
        }

        @Override
        public MeasurementStatus status() {
            return Reason.NO_RULE_DRAWS_A_LINE.status();
        }

        @Override
        public Reason reason() {
            return Reason.NO_RULE_DRAWS_A_LINE;
        }

        @Override
        public List<BorderAssessment> at() {
            return List.of();
        }
    }

    /** No line came back and the reading did not run out. */
    record Unresolved() implements BoundaryDerivation {

        @Override
        public MeasurementStatus status() {
            return Reason.THE_READING_DID_NOT_RUN_OUT.status();
        }

        @Override
        public Reason reason() {
            return Reason.THE_READING_DID_NOT_RUN_OUT;
        }

        @Override
        public List<BorderAssessment> at() {
            return List.of();
        }
    }

    /** This behavior has no positions of its own for a line to be drawn on. */
    record NoSubject() implements BoundaryDerivation {

        @Override
        public MeasurementStatus status() {
            return Reason.NO_SUBJECT.status();
        }

        @Override
        public Reason reason() {
            return Reason.NO_SUBJECT;
        }

        @Override
        public List<BorderAssessment> at() {
            return List.of();
        }
    }

    /** What the measure came to, from what it found and whether its reading ran out. */
    static BoundaryDerivation of(List<BorderAssessment> at, MeasureClosure.OfTheBorder closure) {
        if (closure instanceof MeasureClosure.OfTheBorder.Closed closed) {
            return at.isEmpty() ? new Absent(closed) : new Complete(at);
        }
        return at.isEmpty() ? new Unresolved() : new Partial(at);
    }
}
