package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowOutcome;
import souther.compiler.partition.Axis;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.BoundaryObligation;
import souther.compiler.partition.GuardThresholds;
import souther.compiler.partition.OriginRef;
import souther.compiler.partition.PartitionClass;
import souther.compiler.partition.Partitions;
import souther.compiler.partition.RowClasses;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Measuring one behavior's rows against the distinctions its model draws.
 *
 * <p>Each position is measured on its own. A row that could not be read at one position still says
 * what it says at the others, so an unreadable value leaves that axis undecided and nothing else.
 */
final class Coverages {

    /**
     * The positions one behavior is measured at, with what its own comparisons divide them into.
     *
     * <p>Asked here rather than worked out again wherever it is needed. What a report says is not
     * covered and what a generator writes a row for have to be the same positions and the same classes,
     * and two derivations of them would be two chances to disagree.
     */
    static Partitions.Partitioning partitioningOf(Ast.SpecBehavior behavior, Sig sig, Symbols symbols,
                                                  Core body, CoverageSites.Plan plan) {
        List<String> parameters = behavior.params().stream().map(Ast.Param::name).toList();
        Partitions.Partitioning partitioning = Partitions.of(behavior, sig, symbols);
        if (body == null) {
            return partitioning;
        }
        return Partitions.withThresholds(partitioning,
                GuardThresholds.of(behavior.name(), body, plan, parameters, symbols), symbols);
    }

    /**
     * @param armsMeasured whether the rows were run against classes that record which arms they went
     *                     through. A boundary a {@code guard} drew is not decided without that: the
     *                     value being written is not the same as the comparison having been evaluated.
     */
    static PartitionEvidence of(Ast.SpecBehavior behavior, Sig sig, Symbols symbols, Core body,
                                CoverageSites.Plan plan, souther.compiler.query.Adequacy.Observed observed,
                                boolean armsMeasured) {
        List<RowOutcome> rows = observed.rows();
        List<String> parameters = behavior.params().stream().map(Ast.Param::name).toList();
        Partitions.Partitioning partitioning = partitioningOf(behavior, sig, symbols, body, plan);

        List<PartitionEvidence.AxisCoverage> axes = new ArrayList<>();
        List<PartitionEvidence.BoundaryCoverage> boundaries = new ArrayList<>();
        List<String> notDerivable = new ArrayList<>();

        List<Axis> divided = new ArrayList<>();
        for (Axis axis : partitioning.axes()) {
            if (!axis.measurable()) {
                notDerivable.add(axis.path().toString());
                continue;
            }
            if (axis.derivable()) {
                axes.add(coverageOf(axis, parameters, rows, observed.complete()));
                divided.add(axis);
            }
            boundaries.addAll(boundariesOf(axis, parameters, rows, symbols,
                    armsMeasured && observed.complete()));
        }
        return new PartitionEvidence(axes, boundaries, pairsOf(divided, parameters, rows),
                notDerivable, partitioning.omitted());
    }

    /** How many pairs of classes across two positions the rows are enough to sit in at once. */
    private static final int PAIR_LIMIT = 20_000;

    /**
     * The two-class combinations the rows reach.
     *
     * <p>A combination a row sits in is <em>proven reachable</em>, and the row is the proof. One no row
     * sits in has not been shown unreachable — nothing has tried to build a value for it — so it is
     * unknown rather than missing. The difference matters: calling it unreachable flatters the number,
     * and calling it missing sends the author after a row that may not exist.
     *
     * <p>Pairs, rather than the full product, for the reason pairwise testing exists: most rules that
     * two inputs are involved in are decided by those two, and the product of every input is more rows
     * than anyone writes. A behavior with one divided position has no pairs at all, which is why the
     * single-position coverage is measured on its own and not derived from this.
     */
    private static PartitionEvidence.PairSpace pairsOf(List<Axis> axes, List<String> parameters,
                                                       List<RowOutcome> rows) {
        long total = 0;
        for (int i = 0; i < axes.size(); i++) {
            for (int j = i + 1; j < axes.size(); j++) {
                total += (long) axes.get(i).classes().size() * axes.get(j).classes().size();
            }
        }
        if (total == 0) {
            return PartitionEvidence.PairSpace.NONE;
        }
        if (total > PAIR_LIMIT) {
            return new PartitionEvidence.PairSpace((int) Math.min(total, Integer.MAX_VALUE), 0, 0, 0,
                    (int) Math.min(total, Integer.MAX_VALUE), true);
        }
        Set<String> covered = new LinkedHashSet<>();
        for (RowOutcome row : rows) {
            Map<AxisId, Classification> where = RowClasses.of(row, parameters, axes);
            for (int i = 0; i < axes.size(); i++) {
                for (int j = i + 1; j < axes.size(); j++) {
                    String left = classIn(where, axes.get(i));
                    String right = classIn(where, axes.get(j));
                    if (left != null && right != null) {
                        // Which positions, and not only which classes. A class id is unique within
                        // its axis and not across axes — three `Flag` inputs all have a `Yes` — so a
                        // key of two class names alone collapses every pair one row covers into one.
                        covered.add(i + "/" + left + " " + j + "/" + right);
                    }
                }
            }
        }
        int reached = covered.size();
        return new PartitionEvidence.PairSpace((int) total, reached, reached, 0,
                (int) total - reached, false);
    }

    private static String classIn(Map<AxisId, Classification> where, Axis axis) {
        return where.get(axis.id()) instanceof Classification.Classified in ? in.classId() : null;
    }

    private static PartitionEvidence.AxisCoverage coverageOf(Axis axis, List<String> parameters,
                                                             List<RowOutcome> rows,
                                                             boolean everythingWasSeen) {
        Set<String> covered = new LinkedHashSet<>();
        int unclassified = 0;
        for (RowOutcome row : rows) {
            Classification where = RowClasses.of(row, parameters, List.of(axis)).get(axis.id());
            if (where instanceof Classification.Classified in) {
                covered.add(in.classId());
            } else {
                unclassified++;
            }
        }
        MeasurementStatus status = rows.isEmpty() && everythingWasSeen ? MeasurementStatus.UNAVAILABLE
                : unclassified == 0 && everythingWasSeen ? MeasurementStatus.COMPLETE
                        : MeasurementStatus.PARTIAL;
        return new PartitionEvidence.AxisCoverage(axis.id().toString(), axis.path().toString(),
                axis.classes().stream().map(PartitionClass::id).toList(), covered, unclassified,
                status);
    }

    /**
     * Whether a row was written at each boundary.
     *
     * <p>An invariant's bound is met by writing the value: outside it nothing can be constructed, so
     * the value is the whole of what there is to reach. A guard's is not — the comparison has to have
     * been evaluated, and a row can carry the exact value and never reach the guard that cares about
     * it because an earlier branch went the other way. Nothing measures that until the arms are
     * instrumented, so a guard's boundary reports as unavailable rather than as met or missed.
     */
    private static List<PartitionEvidence.BoundaryCoverage> boundariesOf(
            Axis axis, List<String> parameters, List<RowOutcome> rows, Symbols symbols,
            boolean armsMeasured) {
        List<PartitionEvidence.BoundaryCoverage> out = new ArrayList<>();
        for (BoundaryObligation each : Partitions.obligationsOf(axis, symbols)) {
            boolean available = !rows.isEmpty()
                    && (!(each.origin() instanceof OriginRef.GuardOrigin) || armsMeasured);
            Met met = !available ? Met.UNDECIDED : switch (each.origin()) {
                case OriginRef.GuardOrigin g -> evaluatedAt(axis, parameters, rows, each.value(), g);
                default -> writtenAt(axis, parameters, rows, each.value());
            };
            out.add(new PartitionEvidence.BoundaryCoverage(idOf(each.axis()),
                    each.origin().describe(), each.side(), plain(each.value()),
                    met == Met.YES,
                    met == Met.UNDECIDED ? MeasurementStatus.UNAVAILABLE
                            : met == Met.UNREADABLE ? MeasurementStatus.PARTIAL
                                    : MeasurementStatus.COMPLETE));
        }
        return out;
    }

    /**
     * Whether a row was at a boundary, and whether that could be told at all.
     *
     * <p>Three answers, because a value the observer could not read is not a value that missed. A row
     * writing the very number the rule names, whose observation was cut short by a limit somewhere
     * else in the same input, reads as "no row is at this boundary" — which is a sentence about the
     * model that is not true.
     */
    private enum Met { YES, NO, UNREADABLE, UNDECIDED }

    /**
     * Whether a row wrote the boundary value <em>and</em> got as far as the comparison that cares
     * about it.
     *
     * <p>Both, because either alone is a different claim. A row can hand a behavior exactly 100000 and
     * take an earlier branch that never reaches {@code cost <= 100000}, and counting that as having
     * tried the boundary would report a rule as exercised that nothing has run. Reaching either arm of
     * the {@code if} is enough: the comparison was evaluated to get to either one.
     */
    private static Met evaluatedAt(Axis axis, List<String> parameters, List<RowOutcome> rows,
                                   ObservedValue boundary, OriginRef.GuardOrigin origin) {
        boolean unreadable = false;
        for (RowOutcome row : rows) {
            ObservedValue at = RowClasses.valueAt(row, parameters, axis.path());
            if (!readable(at)) {
                unreadable = true;
                continue;
            }
            if (sameNumber(at, boundary)
                    && (row.hits().contains(origin.guard().siteIndexThen())
                            || row.hits().contains(origin.guard().siteIndexElse()))) {
                return Met.YES;
            }
        }
        return unreadable ? Met.UNREADABLE : Met.NO;
    }

    /** The boundaries a row could have been written at and demonstrably none was. A guard's line is
     * not one of these — whether a row met it is not decided by the value alone — and neither is one
     * whose position some row wrote unreadably, since a row generated for it may be a row that is
     * already there. */
    static List<BoundaryObligation> unmet(Axis axis, List<String> parameters, List<RowOutcome> rows,
                                          Symbols symbols) {
        List<BoundaryObligation> out = new ArrayList<>();
        for (BoundaryObligation each : Partitions.obligationsOf(axis, symbols)) {
            if (!(each.origin() instanceof OriginRef.GuardOrigin)
                    && writtenAt(axis, parameters, rows, each.value()) == Met.NO) {
                out.add(each);
            }
        }
        return out;
    }

    private static Met writtenAt(Axis axis, List<String> parameters, List<RowOutcome> rows,
                                 ObservedValue boundary) {
        boolean unreadable = false;
        for (RowOutcome row : rows) {
            ObservedValue at = RowClasses.valueAt(row, parameters, axis.path());
            if (readable(at)) {
                if (sameNumber(at, boundary)) {
                    return Met.YES;
                }
            } else {
                unreadable = true;
            }
        }
        return unreadable ? Met.UNREADABLE : Met.NO;
    }

    /** Whether an observation says what the value was. A limit reached elsewhere in the same input
     * leaves this position truncated, and a truncation is not a number that missed. */
    private static boolean readable(ObservedValue at) {
        return at != null && !(at instanceof ObservedValue.Unknown)
                && !(at instanceof ObservedValue.Truncated);
    }

    /** A newtype and the number it wraps are the same value at this position, which is how the row
     * writes it and how the boundary was read. */
    private static boolean sameNumber(ObservedValue a, ObservedValue b) {
        java.math.BigDecimal left = numberOf(a);
        java.math.BigDecimal right = numberOf(b);
        return left != null && right != null && left.compareTo(right) == 0;
    }

    private static java.math.BigDecimal numberOf(ObservedValue v) {
        return switch (v) {
            case ObservedValue.Integer i -> java.math.BigDecimal.valueOf(i.value());
            case ObservedValue.Decimal d -> d.value();
            case ObservedValue.Constructed c when c.field("value") != null -> numberOf(c.field("value"));
            case null, default -> null;
        };
    }

    private static String idOf(AxisId axis) {
        return axis.toString();
    }

    /** A boundary as the author would write it, not as a record prints itself. */
    private static String plain(ObservedValue value) {
        java.math.BigDecimal number = numberOf(value);
        return number == null ? String.valueOf(value) : number.stripTrailingZeros().toPlainString();
    }

    private Coverages() {}
}
