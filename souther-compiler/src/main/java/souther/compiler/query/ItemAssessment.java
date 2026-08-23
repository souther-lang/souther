package souther.compiler.query;

import souther.compiler.partition.Criterion;
import souther.compiler.partition.Generator;
import souther.compiler.partition.NotOwedReason;

import java.util.List;

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
    record Owed(Criterion criterion, Measurement<Coverage> coverage, Writability writability,
                Attempt attempt) implements ItemAssessment {}

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

        /**
         * No row that could be read is at the point.
         *
         * <p>Named for what was seen and not for what is so. It was {@code Missed}, which meant
         * "every row that bears on this position was read, and none is at the point" — a claim about
         * the reading as well as about the rows, made by the value itself. Beside it sat
         * {@code Undecided} for the case where the reading was not whole, and the two were one
         * question asked twice: what was found, and how far the finding can be trusted.
         *
         * <p>Now the second is the measurement's. {@code Complete(NoHit)} is what {@code Missed}
         * claimed and {@code Partial(NoHit, ...)} is what {@code Undecided} said, and neither the
         * name nor a reader has to carry the difference.
         */
        record NoHit() implements Coverage {}

        /** Why the question was not put. */
        enum NotAsked implements souther.compiler.observe.NotMeasuredReason {
            /** The build did not ask for the arms, and a line a fork drew is met by reaching the
             *  comparison rather than by writing the value. Never a reason for an invariant's line,
             *  which needs no arms. */
            ARMS_NOT_ASKED,
            /** No row names this behavior. */
            NO_ROWS
        }

        /** Why the question was put and could not be answered. */
        enum CouldNotAsk implements souther.compiler.observe.FailureReason {
            /** The rows ran without instrumentation, so no row can be shown to have reached the
             *  comparison. Never a reason for an invariant's line. */
            ARMS_UNREADABLE
        }

        static boolean hit(Measurement<Coverage> coverage) {
            return coverage.made().orElse(null) instanceof Hit;
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

        /**
         * What a search of the region came to, whichever way it came out.
         *
         * <p>The boundary is which side of the search an outcome is on, and it is a type because it
         * was a sentence. A candidate is composed by walking the region, so everything found out
         * afterwards — a row that was accepted, a row that was refused, decoders that could not be
         * reached — is an outcome of a search that ran and carries what it ran over. What was
         * written instead was a comment saying so, and the one outcome that arrived by a different
         * route was filed as a search nobody made and dropped its region on the way.
         */
        sealed interface Searched extends Attempt {

            /** Where the row was looked for, and what the way to the point took in and could not. */
            souther.compiler.partition.RegionForARow region();
        }

        /** A value at the point, built and accepted by the module's own decoders. */
        record Built(Generator.GeneratedRow row,
                     souther.compiler.partition.RegionForARow region) implements Searched {}

        /**
         * The search ran and no row came of it.
         *
         * <p>Named for what happened and not for one of the ways it happens. Every candidate being
         * refused is one of them; a point with no value to write at all, and a search that stopped
         * before it got here, are the others, and only the first is the decoder saying anything. A
         * name that said "refused" would invite a reader to take the other two for a decision the
         * decoder made — which is the mistake this type exists to prevent, one size down.
         *
         * <p>What a search that settled nothing was looking over is the half of the answer that
         * says how much the other half is worth, so it carries the region like every other outcome
         * of a search.
         */
        record Unresolved(Generator.UnresolvedCombination why,
                          souther.compiler.partition.RegionForARow region) implements Searched {}

        /** Nothing was tried, and why not. Separate from a refusal because they license different
         * sentences: one is a fact about values, the other is a fact about this run. */
        record NotAttempted(Reason reason) implements Attempt {}

        enum Reason {
            /** A row already sits at the point. There is nothing to find out and nothing to offer. */
            A_ROW_IS_ALREADY_THERE,
            /** The point was not measured against the rows, so no row here is owed to anybody yet. */
            NOT_MEASURED,
            /** The module's classes were not there to build against. */
            NO_CLASSES
            // The decoders being out of reach was one of these and is not. It is found by running a
            // candidate, and a candidate is something a search of the region already produced — so
            // it is a search that came to nothing, which is `Unresolved`, and it says so in the
            // generator's own words. Left here, it was the one search whose region went unrecorded.
        }

        /**
         * What the search ran over that the way to the point does not account for.
         *
         * <p>Asked of the attempt because the attempt is what holds both halves: which conditions
         * were left out of the region, and whether this outcome is one they bear on. Answered at a
         * renderer instead, the two halves were a pair of conditions written into a sentence, and
         * the only way to ask what they came to was to compile a model that produced the sentence.
         *
         * <p>Empty where nothing was left out, and empty where the outcome settles the point on its
         * own: a walk of the whole of what the rules leave that reaches no value proves there is
         * nothing to find whether or not the box it walked held rows that never arrive, since an
         * empty box leaves what it contains empty too. Empty for a row that was built, which is a
         * point answered rather than a search to account for, and for a search nobody made.
         */
        default List<souther.compiler.partition.OnTheWay.Declined> unaccountedFor() {
            return switch (this) {
                case Built _, NotAttempted _ -> List.of();
                case Unresolved left -> left.why().reason().provesInfeasible()
                        ? List.of() : left.region().declined();
            };
        }
    }

    /** This point's own measurement of whether a row is at it, or a settled nothing where no row is
     *  owed here at all. */
    default Measurement<Coverage> weakeningSource() {
        return this instanceof Owed owed ? owed.coverage()
                : new Measurement.Complete<>(new Coverage.NoHit());
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
    default WeakeningSet weakening() {
        return switch (this) {
            // A point nobody is owed a row at went without nothing: the question was put to the
            // model and the model answered it. Counted as unmeasured, every bound in a corpus would
            // hold its behavior open for a measurement nobody was ever going to make.
            case NotOwed _ -> WeakeningSet.none();
            case Owed owed -> owed.coverage().weakening();
        };
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
     * than where the model does — and a point nobody measured is not one either. Neither is one
     * missed by rows some of which could not be read: that is a measurement made in part, and what
     * it did not find is undecided rather than absent.
     */
    default boolean isUnmetGap() {
        return this instanceof Owed owed
                && owed.coverage() instanceof Measurement.Complete<Coverage> whole
                && whole.value() instanceof Coverage.NoHit
                && owed.writability().known();
    }
}
