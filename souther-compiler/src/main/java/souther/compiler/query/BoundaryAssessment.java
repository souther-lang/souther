package souther.compiler.query;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.BoundaryObligation;
import souther.compiler.partition.Generator;

import java.math.BigDecimal;

/**
 * Everything known about one boundary a rule drew: whether a row sits at it, and whether a row can be
 * written there at all.
 *
 * <p>Two answers rather than one word. They are established by different means and fail to be
 * established for different reasons: a row at the value is read off what this compilation ran, and
 * whether such a row can exist is settled by putting a value through the decoder. Writing the pair out
 * as a single state means writing the product of the two by hand, and the product has combinations
 * nothing rules out — a value nothing has been written at that something has built, and a value a row
 * sits on whose position nothing could promise.
 *
 * <p>One of these per obligation, made in one place. What a report prints, what a build is warned
 * about and what the generator offers are three readings of this and not three measurements.
 */
public record BoundaryAssessment(BoundaryObligation obligation, Coverage coverage,
                                 Writability writability) {

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
        enum Reason {
            /** The build did not ask for the arms, and a guard's line is met by reaching the
             *  comparison rather than by writing the value. Never a reason for an invariant's line,
             *  which needs no arms. */
            ARMS_NOT_ASKED,
            /** The rows ran without instrumentation, so no row can be shown to have reached the
             *  comparison. Never a reason for an invariant's line. */
            ARMS_UNREADABLE,
            /** No row names this behavior. */
            NO_ROWS
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

        /** A value with this edge in it was built through the module's own decoder. The row is kept
         * because it is also the row an author is offered — one attempt, two readers. */
        record WitnessedByConstruction(Generator.GeneratedRow row) implements Writability {}

        /** Nothing has shown a row can be written here. Not a claim that none can. */
        record Unknown(Reason reason, String detail) implements Writability {

            public static Unknown of(Reason reason) {
                return new Unknown(reason, null);
            }

            /** Why nothing was shown, which decides what an author can do about it. */
            public enum Reason {
                /** Candidates were built and the decoder refused every one of them. Another value of
                 *  the same edge may well build. */
                REFUSED,
                /** No value at all can be written at some position of the row. */
                NO_REPRESENTATIVE,
                /** The search stopped before reaching it. */
                SEARCH_LIMIT,
                /** Nothing was built against: the module's classes or the runtime were not there. */
                NOT_ATTEMPTED
            }
        }

        /** Whether a row is known to be writable here. False leaves it open, never closed. */
        default boolean known() {
            return !(this instanceof Unknown);
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
            case Coverage.NotMeasured _ -> MeasurementStatus.UNAVAILABLE;
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
        return obligation.axis().path() + " = " + value();
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
