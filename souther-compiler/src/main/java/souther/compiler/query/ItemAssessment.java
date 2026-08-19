package souther.compiler.query;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.partition.Criterion;
import souther.compiler.partition.Generator;
import souther.compiler.partition.NotOwedReason;

/**
 * Everything known about one of the four coverage items of a border.
 *
 * <p>Owed or not, and the difference is the shape and not a field. A point nobody is owed a row at
 * has no coverage to report, nothing to say about whether a row could be written there and no search
 * to account for — so it carries none of those, and a state saying the rules refuse this point and a
 * row is at it cannot be built. Held as one record with a reason beside the measurements, that state
 * is one field away at every place that makes one.
 *
 * <p>Where a row is owed, three answers rather than one, because they are about three things and are
 * established by three different means. What the rows showed is read off what this compilation ran.
 * What is proven about a value existing there comes from the rules, or from a value that went through
 * the decoder. What the search did is what the search did — and it is kept even where it changed
 * neither of the others, because a point the rules already prove is still one a search can fail to
 * produce a row for, and the person who wanted that row is owed the reason.
 */
public sealed interface ItemAssessment {

    /** No row is owed here, and this is what settles it. */
    record NotOwed(NotOwedReason reason) implements ItemAssessment {}

    /** A row is owed, and this is what became of it. */
    record Owed(Criterion criterion, Coverage coverage, Writability writability, Attempt attempt)
            implements ItemAssessment {}

    /**
     * Whether a row is at this point, and whether that could be told.
     *
     * <p>A point an invariant drew is met by a row whose value is the boundary. One a fork of a body
     * drew is not: the comparison has to have been evaluated as well, because a value can reach the
     * input of a behavior without reaching the guard that cares about it. That is a fact about the
     * rule and holds of all four of the border's points.
     */
    sealed interface Coverage {

        /** A row is at the point, and — where a fork drew the line — went through the comparison.
         * Found is found: a row settles this whatever else went unread. */
        record Hit() implements Coverage {}

        /** Every row that bears on this position was read, and none is at the point. */
        record Missed() implements Coverage {}

        /** Some row's value here could not be read, or some row was never seen. What is not found is
         * then undecided rather than absent. */
        record Undecided() implements Coverage {}

        /** The question was not put. */
        record NotMeasured(Reason reason) implements Coverage {}

        /** Why a point has no answer. */
        enum Reason implements souther.compiler.observe.MeasureReason {
            /** The build did not ask for the arms, and a line a fork drew is met by reaching the
             *  comparison rather than by writing the value. Never a reason for an invariant's line,
             *  which needs no arms. */
            ARMS_NOT_ASKED(MeasurementStatus.NOT_MEASURED),
            /** The rows ran without instrumentation, so no row can be shown to have reached the
             *  comparison. Never a reason for an invariant's line. */
            ARMS_UNREADABLE(MeasurementStatus.NOT_MEASURED),
            /** No row names this behavior. */
            NO_ROWS(MeasurementStatus.NOT_MEASURED);

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
     * Whether a row can be written at the point, and what says so.
     *
     * <p>Three ways to know and one way not to. A refusal is not among the ways to know: the decoder
     * refusing every candidate that was tried says nothing about the candidates that were not, so a
     * point whose values were all refused stays unknown rather than becoming impossible. Nothing here
     * can say a point is unwritable, and that is the point of the type — what says a point cannot be
     * written at is the border refusing to owe it at all.
     */
    sealed interface Writability {

        /** Every rule reaching the value this position sits in was read, and the point is inside what
         * they leave. Nothing had to be built to know it. */
        record ProvenByProjection() implements Writability {}

        /** A row already sits at the point, which is a value that went through the decoder. The
         * strongest of these and the only one that costs nothing to find. */
        record WitnessedByRow() implements Writability {}

        /** A value at this point was built through the module's own decoder. What was built is in
         * {@link Owed#attempt()} and not here: this says which evidence settled the question, and the
         * evidence itself has one home. */
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
     * What was built at this point, and what came of it.
     *
     * <p>Its own answer and not a shade of {@link Writability}. A point the projection already proved
     * is one a search can still fail to reach — the two are about different things, and a reader that
     * recovered the attempt from the verdict would find nothing to say about a row it could not
     * produce at a point it knows exists. The report reads the verdict; {@code --generate} reads this.
     *
     * <p>Made once. The row a person is offered and the value that witnessed the point are the same
     * value, built one time and read twice.
     */
    sealed interface Attempt {

        /** A value at the point, built and accepted by the module's own decoders. */
        record Built(Generator.GeneratedRow row) implements Attempt {}

        /**
         * The search ran and no row came of it.
         *
         * <p>Named for what happened and not for one of the ways it happens. Every candidate being
         * refused is one of them; a point with no value to write at all, and a search that stopped
         * before it got here, are the others, and only the first is the decoder saying anything. A
         * name that said "refused" would invite a reader to take the other two for a decision the
         * decoder made — which is the mistake this type exists to prevent, one size down.
         */
        record Unresolved(Generator.UnresolvedCombination why) implements Attempt {}

        /** Nothing was tried, and why not. Separate from a refusal because they license different
         * sentences: one is a fact about values, the other is a fact about this run. */
        record NotAttempted(Reason reason) implements Attempt {}

        enum Reason {
            /** A row already sits at the point. There is nothing to find out and nothing to offer. */
            A_ROW_IS_ALREADY_THERE,
            /** The point was not measured against the rows, so no row here is owed to anybody yet. */
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
     *
     * <p>A point nobody is owed a row at is complete: the question was put to the model and the model
     * answered it. Read as unmeasured, every bound in a corpus would hold its behavior open for a
     * measurement nobody was ever going to make.
     */
    default MeasurementStatus status() {
        return switch (this) {
            case NotOwed _ -> MeasurementStatus.COMPLETE;
            case Owed owed -> switch (owed.coverage()) {
                case Coverage.NotMeasured absent -> absent.reason().status();
                case Coverage.Undecided _ -> MeasurementStatus.PARTIAL;
                case Coverage.Hit _, Coverage.Missed _ -> MeasurementStatus.COMPLETE;
            };
        };
    }

    /**
     * Why the coverage half has no answer, or null where it has one.
     *
     * <p>Beside {@link #status()} and derived like it. Every measure that comes back without a number
     * is asked why, in the same words, and a point that could say {@code UNAVAILABLE} without saying
     * what stopped it would be the one measure a reader has to guess about.
     */
    default Coverage.Reason whyNotMeasured() {
        return this instanceof Owed owed && owed.coverage() instanceof Coverage.NotMeasured absent
                ? absent.reason() : null;
    }

    /** Whether a row is owed here at all, and so whether the three answers beside it exist. */
    default boolean owed() {
        return this instanceof Owed;
    }

    /**
     * Whether this is a row an author is owed: the point was measured and missed, and something has
     * shown a row can be written there.
     *
     * <p>The two halves are asked of the two answers rather than of one flattened state. A missed
     * point nothing promises is writable is not a gap — the point is where the reading stopped rather
     * than where the model does — and a point nobody measured is not one either.
     */
    default boolean isUnmetGap() {
        return this instanceof Owed owed && owed.coverage() instanceof Coverage.Missed
                && owed.writability().known();
    }
}
