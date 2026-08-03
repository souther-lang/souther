package souther.compiler.query;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.partition.BoundaryObligation;

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
 * @param omitted      positions dropped for being past the axis limit
 */
public record PartitionEvidence(List<AxisCoverage> axes, List<BoundaryCoverage> boundaries,
                                PairSpace pairs, List<String> notDerivable,
                                List<Incompleteness> omitted) {

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
     */
    public record PairSpace(int total, int covered, int witnessedFeasible, int provenInfeasible,
                            int unknown, boolean truncated) {

        public static final PairSpace NONE = new PairSpace(0, 0, 0, 0, 0, false);

        /** Whether a single ratio would say anything. With unknowns in the denominator it would not. */
        public boolean decided() {
            return unknown == 0 && !truncated;
        }
    }

    /**
     * How much of one position's partition the rows reach.
     *
     * @param unclassifiedRows rows whose value at this position could not be read. Above zero, an
     *                         unreached class is undecided rather than unreached.
     */
    public record AxisCoverage(String axis, String path, List<String> classes, Set<String> covered,
                               int unclassifiedRows, MeasurementStatus status) {

        public AxisCoverage {
            classes = List.copyOf(classes);
            covered = Set.copyOf(covered);
        }

        public List<String> uncovered() {
            return classes.stream().filter(c -> !covered.contains(c)).toList();
        }
    }

    /**
     * One value a row has to be written at, and whether one was.
     *
     * @param status {@code UNAVAILABLE} where the rule is a guard: meeting it takes more than writing
     *               the value — the comparison has to have been evaluated — and nothing measures that
     *               until the branches are instrumented.
     */
    public record BoundaryCoverage(String axis, String origin, BoundaryObligation.BoundarySide side,
                                   String value, boolean hit, MeasurementStatus status) {}
}
