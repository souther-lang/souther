package souther.compiler.query;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.partition.BoundaryObligation;
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
 * @param notDerivable positions the model does not divide, named so a report can say what it could
 *                     not measure rather than passing over it
 * @param omitted      positions dropped for being past the axis limit, with what dropping each
 *                     one cost — a position that was carrying a boundary leaves the rows there
 *                     unmeasured rather than covered
 */
public record PartitionEvidence(List<AxisCoverage> axes, List<BoundaryCoverage> boundaries,
                                PairSpace pairs, List<String> notDerivable,
                                List<Partitions.OmittedAxis> omitted) {

    public static final PartitionEvidence NONE = new PartitionEvidence(List.of(), List.of(),
            PairSpace.NONE, List.of(), List.of());

    public PartitionEvidence {
        axes = List.copyOf(axes);
        boundaries = List.copyOf(boundaries);
        notDerivable = List.copyOf(notDerivable);
        omitted = List.copyOf(omitted);
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
        public enum Reason {
            /** No row names this behavior, so nothing sits anywhere. */
            NO_ROWS
        }

        public static final PairSpace NONE =
                new PairSpace(0, 0, 0, 0, 0, false, MeasurementStatus.COMPLETE, null);

        public static PairSpace unavailable(int total, Reason reason) {
            return new PairSpace(total, 0, 0, 0, total, false, MeasurementStatus.UNAVAILABLE, reason);
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
     * One class the body says it does not answer for, and why.
     *
     * <p>{@code reasons} is every reason on the paths that abort, and usually one. An arm made of a
     * {@code match} whose arms abort for different reasons has no single reason, and naming the one
     * written above the others would describe the class by where the file happens to put it.
     */
    public record ExcludedClass(String classId, List<String> reasons) {

        public ExcludedClass {
            reasons = List.copyOf(reasons);
        }
    }

    /**
     * How much of one position's partition the rows reach.
     *
     * @param classes          the classes a row can be written at. What the model divides the position
     *                         into, less what the body says it does not answer for
     * @param excluded         the classes the body rules out, named so that a report says what it took
     *                         out rather than showing a position with fewer classes than the type has
     * @param unclassifiedRows rows whose value at this position could not be read. Above zero, an
     *                         unreached class is undecided rather than unreached.
     */
    public record AxisCoverage(String axis, String path, List<String> classes, Set<String> covered,
                               List<ExcludedClass> excluded, int unclassifiedRows,
                               MeasurementStatus status, Reason reason) {

        /** Why a position has no coverage numbers. */
        public enum Reason {
            /** No row names this behavior. An absence of evidence is not a set of gaps, so the classes
             *  nothing sits in are not classes nothing reaches. */
            NO_ROWS
        }

        /** What the body rules out is still said. Which classes there are and which the body answers
         * for are facts about the model, and no row has to exist for either. */
        public static AxisCoverage unavailable(String axis, String path, List<String> classes,
                                               List<ExcludedClass> excluded, Reason reason) {
            return new AxisCoverage(axis, path, classes, Set.of(), excluded, 0,
                    MeasurementStatus.UNAVAILABLE, reason);
        }

        public AxisCoverage {
            classes = List.copyOf(classes);
            covered = Set.copyOf(covered);
            excluded = List.copyOf(excluded);
            Unavailable.check(status, reason);
        }

        public List<String> uncovered() {
            return classes.stream().filter(c -> !covered.contains(c)).toList();
        }
    }

    /**
     * One value a row has to be written at, and whether one was.
     *
     * @param reason why it could not be told, where it could not. A guard's line and an invariant's
     *               are not measured the same way and do not fail to be measured for the same
     *               reasons, which is why the two are built along separate paths
     */
    public record BoundaryCoverage(String axis, String origin, BoundaryObligation.BoundarySide side,
                                   String value, boolean hit, MeasurementStatus status,
                                   Reason reason, boolean knownWritable) {

        /** Why a line has no answer. */
        public enum Reason {
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

        public BoundaryCoverage {
            Unavailable.check(status, reason);
        }
    }

}
