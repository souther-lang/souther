package souther.compiler.query;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.BoundaryObligation;
import souther.compiler.partition.Generator;

import java.math.BigDecimal;

/**
 * Everything known about one boundary a rule drew.
 *
 * <p>Three answers rather than one state, because they are about three things and are established by
 * three different means. What the rows showed is read off what this compilation ran. What is proven
 * about a value existing there comes from the rules, or from a value that went through the decoder.
 * What the search did is what the search did — and it is kept even where it changed neither of the
 * others, because an edge the rules already prove is still one a search can fail to produce a row
 * for, and the person who wanted that row is owed the reason.
 *
 * <p>Writing them as a single word means writing the product of three by hand, and the product has
 * combinations nothing rules out: a value nothing has been written at that something built, a value a
 * row sits on whose position nothing could promise, a value the rules prove and no search reached.
 *
 * <p>One of these per obligation, made in one place. What a report prints, what a build is warned
 * about and what the generator offers are three readings of this and not three measurements.
 */
public record BoundaryAssessment(BoundaryObligation obligation, Coverage coverage,
                                 Writability writability, Attempt attempt) {

    /**
     * Whether a row sits at the value, and whether that could be told.
     *
     * <p>An obligation from an invariant is met by a row whose value is the boundary. One from a guard
     * is not: the comparison has to have been evaluated as well, because a value can reach the input of
     * a behavior without reaching the guard that cares about it.
     */
    public sealed interface Coverage {

        /** A row is at the value, and — for a guard's line — went through the comparison. Found is
         * found: a row at the boundary settles this whatever else went unread. */
        record Hit() implements Coverage {}

        /** Every row that bears on this position was read, and none is at the value. */
        record Missed() implements Coverage {}

        /** Some row's value here could not be read, or some row was never seen. What is not found is
         * then undecided rather than absent. */
        record Undecided() implements Coverage {}

        /** The question was not put. */
        record NotMeasured(Reason reason) implements Coverage {}

        /** Why a line has no answer. */
        enum Reason implements souther.compiler.observe.MeasureReason {
            /** The build did not ask for the arms, and a guard's line is met by reaching the
             *  comparison rather than by writing the value. Never a reason for an invariant's line,
             *  which needs no arms. */
            ARMS_NOT_ASKED(MeasurementStatus.NOT_MEASURED),
            /** The rows ran without instrumentation, so no row can be shown to have reached the
             *  comparison. Never a reason for an invariant's line. */
            ARMS_UNREADABLE(MeasurementStatus.NOT_MEASURED),
            /** No row names this behavior. */
            NO_ROWS(MeasurementStatus.NOT_MEASURED),
            /**
             * No arm of the guard separates the rows that reached the comparison from the rows that
             * did not.
             *
             * <p>The second operand of a {@code &&} has this on the side where it is false: the arm
             * a row there lands in is the one every other way of failing the condition lands in too.
             * Never a reason for an invariant's line, and never a claim that the line is not owed —
             * a row at it is still a row somebody should write, and this build has no way to see
             * that they did.
             */
            NO_ARM_WITNESSES_IT(MeasurementStatus.NOT_MEASURED);

            private final MeasurementStatus status;

            Reason(MeasurementStatus status) {
                this.status = status;
            }

            @Override
            public MeasurementStatus status() {
                return status;
            }
        }

        default boolean hit() {
            return this instanceof Hit;
        }
    }

    /**
     * Whether a row can be written at the value, and what says so.
     *
     * <p>Three ways to know and one way not to. A refusal is not among the ways to know: the decoder
     * refusing every candidate that was tried says nothing about the candidates that were not, so a
     * boundary whose values were all refused stays unknown rather than becoming impossible. Nothing
     * here can say a boundary is unwritable, and that is the point of the type.
     */
    public sealed interface Writability {

        /** Every rule reaching the value this position sits in was read, and the edge is inside what
         * they leave. Nothing had to be built to know it. */
        record ProvenByProjection() implements Writability {}

        /** A row already sits at the value, which is a value that went through the decoder. The
         * strongest of these and the only one that costs nothing to find. */
        record WitnessedByRow() implements Writability {}

        /** A value with this edge in it was built through the module's own decoder. What was built is
         * in {@link BoundaryAssessment#attempt()} and not here: this says which evidence settled the
         * question, and the evidence itself has one home. */
        record WitnessedByConstruction() implements Writability {}

        /** Nothing has shown a row can be written here. Not a claim that none can, and it carries no
         * reason of its own — what was tried and what came of it is the attempt's to say. */
        record Unknown() implements Writability {}

        /** Whether a row is known to be writable here. False leaves it open, never closed. */
        default boolean known() {
            return !(this instanceof Unknown);
        }
    }

    /**
     * What was built at this boundary, and what came of it.
     *
     * <p>Its own answer and not a shade of {@link Writability}. An edge the projection already proved
     * is one a search can still fail to reach — the two are about different things, and a reader that
     * recovered the attempt from the verdict would find nothing to say about a row it could not
     * produce at an edge it knows exists. The report reads the verdict; {@code --generate} reads this.
     *
     * <p>Made once. The row a person is offered and the value that witnessed the edge are the same
     * value, built one time and read twice.
     */
    public sealed interface Attempt {

        /** A value with the edge in it, built and accepted by the module's own decoders. */
        record Built(Generator.GeneratedRow row) implements Attempt {}

        /**
         * The search ran and no row came of it.
         *
         * <p>Named for what happened and not for one of the ways it happens. Every candidate being
         * refused is one of them; a position with no value to write at all, and a search that stopped
         * before it got here, are the others, and only the first is the decoder saying anything. A
         * name that said "refused" would invite a reader to take the other two for a decision the
         * decoder made — which is the mistake this type exists to prevent, one size down.
         */
        record Unresolved(Generator.UnresolvedCombination why) implements Attempt {}

        /** Nothing was tried, and why not. Separate from a refusal because they license different
         * sentences: one is a fact about values, the other is a fact about this run. */
        record NotAttempted(Reason reason) implements Attempt {}

        enum Reason {
            /** A row already sits at the value. There is nothing to find out and nothing to offer. */
            A_ROW_IS_ALREADY_THERE,
            /** The line was not measured against the rows, so no row here is owed to anybody yet. */
            NOT_MEASURED,
            /** The module's classes were not there to build against. */
            NO_CLASSES,
            /** The generated classes would not link, so the decoders could not be reached. What
             * the JVM raised is a {@code LinkageError}, and which of its causes it was is not
             * something this can tell. */
            LINKAGE_FAILED
        }
    }

    /**
     * How far the coverage half got, as the one word every measure is totalled under.
     *
     * <p>Derived rather than stored. A report adding up what it could and could not measure asks this
     * of each measure in turn, and a copy of the answer kept beside the answer is a second thing to
     * keep in step.
     */
    public MeasurementStatus status() {
        return switch (coverage) {
            case Coverage.NotMeasured absent -> absent.reason().status();
            case Coverage.Undecided _ -> MeasurementStatus.PARTIAL;
            case Coverage.Hit _, Coverage.Missed _ -> MeasurementStatus.COMPLETE;
        };
    }

    /**
     * Why the coverage half has no answer, or null where it has one.
     *
     * <p>Beside {@link #status()} and derived like it. Every measure that comes back without a number
     * is asked why, in the same words, and a line that could say {@code UNAVAILABLE} without saying
     * what stopped it would be the one measure a reader has to guess about.
     */
    public Coverage.Reason reason() {
        return coverage instanceof Coverage.NotMeasured absent ? absent.reason() : null;
    }

    /** The position this is on, as a report names it. */
    public String axis() {
        return obligation.axis().toString();
    }

    /** The rule that drew the line. */
    public String origin() {
        return obligation.origin().describe();
    }

    public BoundaryObligation.BoundarySide side() {
        return obligation.side();
    }

    /** How a row at this boundary describes itself: where the edge is, and what value it takes. The
     * generator writes these same words on the row it offers, so a row and a note about the boundary
     * it stands for name it the same way. */
    public String label() {
        return obligation.axis().term() + " = " + value();
    }

    /** The value as an author would write it, not as a record prints itself. */
    public String value() {
        BigDecimal number = numberOf(obligation.value());
        return number == null ? String.valueOf(obligation.value())
                : number.stripTrailingZeros().toPlainString();
    }

    /**
     * Whether this is a row an author is owed: the value was measured and missed, and something has
     * shown a row can be written there.
     *
     * <p>The two halves are asked of the two answers rather than of one flattened state. A missed
     * boundary nothing promises is writable is not a gap — the edge is where the reading stopped
     * rather than where the model does — and a boundary nobody measured is not one either.
     */
    public boolean isUnmetGap() {
        return coverage instanceof Coverage.Missed && writability.known();
    }

    /** A newtype and the number it wraps are the same value here, which is how a row writes it and how
     * the boundary was read. */
    private static BigDecimal numberOf(ObservedValue value) {
        return switch (value) {
            case ObservedValue.Integer i -> BigDecimal.valueOf(i.value());
            case ObservedValue.Decimal d -> d.value();
            case ObservedValue.Constructed c when c.field("value") != null -> numberOf(c.field("value"));
            case null, default -> null;
        };
    }
}
