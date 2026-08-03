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

    static PartitionEvidence of(Ast.SpecBehavior behavior, Sig sig, Symbols symbols, Core body,
                                CoverageSites.Plan plan, List<RowOutcome> rows) {
        List<String> parameters = behavior.params().stream().map(Ast.Param::name).toList();
        Partitions.Partitioning partitioning = Partitions.of(behavior, sig, symbols);
        if (body != null) {
            partitioning = Partitions.withThresholds(partitioning,
                    GuardThresholds.of(behavior.name(), body, plan, parameters, symbols), symbols);
        }

        List<PartitionEvidence.AxisCoverage> axes = new ArrayList<>();
        List<PartitionEvidence.BoundaryCoverage> boundaries = new ArrayList<>();
        List<String> notDerivable = new ArrayList<>();

        for (Axis axis : partitioning.axes()) {
            if (!axis.measurable()) {
                notDerivable.add(axis.path().toString());
                continue;
            }
            if (axis.derivable()) {
                axes.add(coverageOf(axis, parameters, rows));
            }
            boundaries.addAll(boundariesOf(axis, parameters, rows, symbols));
        }
        return new PartitionEvidence(axes, boundaries, notDerivable, partitioning.omitted());
    }

    private static PartitionEvidence.AxisCoverage coverageOf(Axis axis, List<String> parameters,
                                                             List<RowOutcome> rows) {
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
        MeasurementStatus status = rows.isEmpty() ? MeasurementStatus.UNAVAILABLE
                : unclassified == 0 ? MeasurementStatus.COMPLETE : MeasurementStatus.PARTIAL;
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
            Axis axis, List<String> parameters, List<RowOutcome> rows, Symbols symbols) {
        List<PartitionEvidence.BoundaryCoverage> out = new ArrayList<>();
        for (BoundaryObligation each : Partitions.obligationsOf(axis, symbols)) {
            boolean guard = each.origin() instanceof OriginRef.GuardOrigin;
            boolean written = !guard && writtenAt(axis, parameters, rows, each.value());
            out.add(new PartitionEvidence.BoundaryCoverage(idOf(each.axis()),
                    each.origin().describe(), each.side(), plain(each.value()), written,
                    guard ? MeasurementStatus.UNAVAILABLE
                            : rows.isEmpty() ? MeasurementStatus.UNAVAILABLE
                                    : MeasurementStatus.COMPLETE));
        }
        return out;
    }

    private static boolean writtenAt(Axis axis, List<String> parameters, List<RowOutcome> rows,
                                     ObservedValue boundary) {
        for (RowOutcome row : rows) {
            ObservedValue at = RowClasses.valueAt(row, parameters, axis.path());
            if (at != null && sameNumber(at, boundary)) {
                return true;
            }
        }
        return false;
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
