package souther.compiler.query;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.partition.Partitions;

import java.util.List;
import java.util.Set;

/**
 * What a behavior's rows reach of the distinctions its model draws.
 *
 * <p>Values only — no classifier, no representative source. What decides a class is a function, and a
 * function held in a memoised answer never compares equal to the same function computed again, so
 * everything downstream would recompute on every ask. What a report needs is the names and the
 * numbers; the functions are used on the way here and left behind.
 *
 * @param axes         one entry per position the model divides
 * @param boundaries   one entry per rule that drew a line, per side of it
 * @param notDerivable positions no class came back for, each saying whether the model divides them
 *                     no way at all or this could not read what it divides them by. Both used to be
 *                     one list of paths, and the sentence written from it claimed the first about
 *                     both
 * @param omitted      positions dropped for being past the axis limit, with what dropping each
 *                     one cost — a position that was carrying a boundary leaves the rows there
 *                     unmeasured rather than covered
 * @param whyUnclassified why the rows counted in {@link AxisCoverage#unclassifiedRows} could not be
 *                     placed. The count is the measurement and this is what it came out of, which
 *                     is why they are two things and not one wider count. Not a report's list of
 *                     reasons: these are what classification observed, and joining them to
 *                     everything else a module could not read happens where that list is built
 */
public record PartitionEvidence(Partitioned partitioned, Bounded bounded,
                                PairSpace pairs,
                                List<souther.compiler.partition.UndividedPosition> notDerivable,
                                List<souther.compiler.inputs.UnreadRule> unread,
                                List<Partitions.OmittedAxis> omitted,
                                List<Incompleteness> whyUnclassified) {


    /**
     * No measure of this kind here at all, which is not a measure that came back empty.
     *
     * <p>What a {@code >->} composition gets. It has no positions of its own for either of these to
     * be about, the way it has no arms, and no row anybody writes would give it one — so the two
     * answer inapplicable, and a verdict that counted them would hold every model with a composition
     * in it open for a measurement that was never anybody's to make.
     */
    public static final PartitionEvidence NONE = new PartitionEvidence(Partitioned.absent(),
            Bounded.absent(), PairSpace.NONE, List.of(), List.of(), List.of(), List.of());

    public PartitionEvidence {
        notDerivable = List.copyOf(notDerivable);
        unread = List.copyOf(unread);
        omitted = List.copyOf(omitted);
        whyUnclassified = List.copyOf(whyUnclassified);
    }

    /** The positions, for a reader that wants them and not what the measure made of itself. */
    public List<AxisCoverage> axes() {
        return partitioned.at();
    }

    /** The lines, likewise. */
    public List<BoundaryAssessment> boundaries() {
        return bounded.at();
    }

    /**
     * The positions this behavior is measured at, and — where there are none — why not.
     *
     * <p>The list alone cannot say. An empty one is what a behavior whose model divides nothing has
     * and what a behavior whose positions could not be read has, and a reader counting entries calls
     * both of them measured and finds no gaps. So the measure answers for itself, and the entries are
     * what it answered with.
     */
    public record Partitioned(List<AxisCoverage> at, MeasurementStatus status, Reason reason) {

        /** Why no position was measured. */
        public enum Reason implements souther.compiler.observe.MeasureReason {
            /** Nothing came back divided. Whether the model draws no line anywhere or the reading
             *  stopped short of one is not something this can tell, and only a proof excludes: the
             *  positions it could not derive are named beside it and may be carrying rules. */
            NO_AXIS_DERIVED(MeasurementStatus.NOT_MEASURED),
            /** This behavior has no positions for the measure to be about — a {@code >->}
             *  composition, which is measured at its stages. */
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

        public static Partitioned of(List<AxisCoverage> at) {
            return at.isEmpty()
                    ? new Partitioned(List.of(), Reason.NO_AXIS_DERIVED.status(),
                            Reason.NO_AXIS_DERIVED)
                    : new Partitioned(at, MeasurementStatus.COMPLETE, null);
        }

        static Partitioned absent() {
            return new Partitioned(List.of(), Reason.NO_SUBJECT.status(), Reason.NO_SUBJECT);
        }

        public Partitioned {
            at = List.copyOf(at);
            Unavailable.check(status, reason);
        }
    }

    /** The lines some rule drew that this behavior is measured at, and — where there are none — why
     * not. The same argument as {@link Partitioned}: an empty list of obligations reads exactly like
     * a measure that was made and found everything met. */
    public record Bounded(List<BoundaryAssessment> at, MeasurementStatus status, Reason reason) {

        /** Why no line was measured. */
        public enum Reason implements souther.compiler.observe.MeasureReason {
            /** No obligation was derived. A model whose bounds sit one type away from the position
             *  the behavior takes has this, and so has one with no bound anywhere; nothing here can
             *  tell them apart, and calling it measured said the rows carrying a model's whole risk
             *  had earned nothing. */
            NO_LINES_DERIVED(MeasurementStatus.NOT_MEASURED),
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

        public static Bounded of(List<BoundaryAssessment> at) {
            return at.isEmpty()
                    ? new Bounded(List.of(), Reason.NO_LINES_DERIVED.status(),
                            Reason.NO_LINES_DERIVED)
                    : new Bounded(at, MeasurementStatus.COMPLETE, null);
        }

        static Bounded absent() {
            return new Bounded(List.of(), Reason.NO_SUBJECT.status(), Reason.NO_SUBJECT);
        }

        public Bounded {
            at = List.copyOf(at);
            Unavailable.check(status, reason);
        }
    }

    /**
     * How many two-class combinations the rows reach, and how much is known about the rest.
     *
     * <p>Three numbers rather than a percentage, because the denominator is not known. A combination
     * a row reaches is proven reachable — the row is the proof. A combination no row reaches has not
     * been shown impossible; nothing has tried to build one. Calling those unreachable would flatter
     * the coverage, and calling them missing would send the author after rows that may not exist.
     *
     * <p>{@link #provenInfeasible} is what a search settled: a combination whose values were tried and
     * refused for a reason that is about the combination, or one ruled out by a constraint. Nothing
     * fills it until something builds candidates, and a candidate that failed to build is not it —
     * another value of the same two classes may well have built.
     *
     * @param truncated whether the space was too large to enumerate, so these numbers describe part
     *                  of it
     * @param status    {@code PARTIAL} where the rows these were counted from are not all the rows
     *                  there were, or not all of them could be placed. Reached is still reached; what
     *                  is not reached is then undecided rather than untried
     */
    public record PairSpace(int total, int covered, int witnessedFeasible, int provenInfeasible,
                            int unknown, boolean truncated, MeasurementStatus status, Reason reason) {

        /** Why the combinations have no numbers. */
        public enum Reason implements souther.compiler.observe.MeasureReason {
            /** No row names this behavior, so nothing sits anywhere. */
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

        public static final PairSpace NONE =
                new PairSpace(0, 0, 0, 0, 0, false, MeasurementStatus.COMPLETE, null);

        public static PairSpace unavailable(int total, Reason reason) {
            return new PairSpace(total, 0, 0, 0, total, false, reason.status(), reason);
        }

        public PairSpace {
            Unavailable.check(status, reason);
        }

        /** Whether a single ratio would say anything. With unknowns in the denominator it would not. */
        public boolean decided() {
            return unknown == 0 && !truncated;
        }
    }



    /**
     * How much of one position's partition the rows reach.
     *
     * @param classes          the classes a row can be written at, which is what the model divides
     *                         the position into: a case its rules refuse is not one of them. Nothing
     *                         a body declares narrows this — what it declared is said beside these
     *                         numbers ({@link ClaimAnnotations}) and never into them
     * @param excluded         the classes the rules rule out and a body's claim named, so that a report says what it took
     *                         out rather than showing a position with fewer classes than the type has
     * @param unclassifiedRows rows whose value at this position could not be read. Above zero, an
     *                         unreached class is undecided rather than unreached.
     */
    public record AxisCoverage(String axis, String path, List<String> classes, Set<String> covered,
                               int unclassifiedRows, MeasurementStatus status, Reason reason) {

        /** Why a position has no coverage numbers. */
        public enum Reason implements souther.compiler.observe.MeasureReason {
            /** No row names this behavior. An absence of evidence is not a set of gaps, so the classes
             *  nothing sits in are not classes nothing reaches. */
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

        /** Which classes there are is a fact about the model, and no row has to exist for it to be
         *  so — which is why a position nothing was measured at still names them. */
        public static AxisCoverage unavailable(String axis, String path, List<String> classes,
                                               Reason reason) {
            return new AxisCoverage(axis, path, classes, Set.of(), 0, reason.status(), reason);
        }

        public AxisCoverage {
            classes = List.copyOf(classes);
            covered = Set.copyOf(covered);
            Unavailable.check(status, reason);
        }

        public List<String> uncovered() {
            return classes.stream().filter(c -> !covered.contains(c)).toList();
        }
    }

}
