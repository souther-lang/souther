package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.observe.Classification;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowOutcome;
import souther.compiler.partition.Axis;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.BoundaryObligation;
import souther.compiler.partition.Exclusions;
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
                                                  Core body, CoverageSites.Plan plan,
                                                  Exclusions excluded) {
        List<String> parameters = behavior.params().stream().map(Ast.Param::name).toList();
        Partitions.Partitioning partitioning = Partitions.of(behavior, sig, symbols, excluded);
        if (body == null) {
            return partitioning;
        }
        return Partitions.withThresholds(partitioning,
                GuardThresholds.of(behavior.name(), body, plan, parameters, symbols).thresholds(),
                symbols);
    }

    /**
     * @param boundaries what was established about every line this behavior's rules drew, made once
     *                   by {@link souther.compiler.query.Adequacy.Boundaries} and read here. Measuring
     *                   a line takes putting a value through the module's decoders, which is not
     *                   something a coverage count can do on its own and not something that should
     *                   happen twice.
     */
    static PartitionEvidence of(Ast.SpecBehavior behavior, Sig sig, Symbols symbols, Core body,
                                CoverageSites.Plan plan, souther.compiler.query.Adequacy.Observed observed,
                                List<BoundaryAssessment> boundaries, Exclusions excluded) {
        List<RowOutcome> rows = observed.rows();
        List<String> parameters = behavior.params().stream().map(Ast.Param::name).toList();
        Partitions.Partitioning partitioning =
                partitioningOf(behavior, sig, symbols, body, plan, excluded);

        List<PartitionEvidence.AxisCoverage> axes = new ArrayList<>();
        List<String> notDerivable = new ArrayList<>();

        List<Axis> divided = new ArrayList<>();
        Readings readings = Readings.of(rows, parameters, partitioning.axes(),
                observed.someRowsUnseen());
        for (Axis axis : partitioning.axes()) {
            if (!axis.measurable()) {
                notDerivable.add(axis.path().toString());
                continue;
            }
            if (axis.derivable()) {
                axes.add(coverageOf(axis, readings, excluded));
                divided.add(axis);
            }
        }
        return new PartitionEvidence(axes, boundaries, pairsOf(divided, readings),
                notDerivable, partitioning.omitted());
    }

    /**
     * What every row said at every position, read once.
     *
     * <p>The measures below were putting the same question to the rows — which class is this row in,
     * here — and answering the follow-up differently. The single-position coverage counted the rows
     * that could not say and reported them as undecided; the combinations left those rows out and
     * reported what remained as untried. One reading, so that a row nothing could place is the same
     * fact wherever it is read.
     *
     * @param someRowsUnseen rows that were never observed at all, which no reading can show
     */
    private record Readings(List<Map<AxisId, Classification>> byRow, boolean someRowsUnseen) {

        static Readings of(List<RowOutcome> rows, List<String> parameters, List<Axis> axes,
                           boolean someRowsUnseen) {
            List<Map<AxisId, Classification>> read = new ArrayList<>();
            for (RowOutcome row : rows) {
                read.add(RowClasses.of(row, parameters, axes));
            }
            return new Readings(List.copyOf(read), someRowsUnseen);
        }

        boolean noRows() {
            return byRow.isEmpty();
        }

        /** Which class a row fell in at one position, or null where it did not say. */
        static String classIn(Map<AxisId, Classification> where, Axis axis) {
            return where.get(axis.id()) instanceof Classification.Classified in ? in.classId() : null;
        }

        /** How many rows could not say where they were at this position. */
        int couldNotSay(Axis axis) {
            return (int) byRow.stream().filter(where -> classIn(where, axis) == null).count();
        }

        /**
         * Whether every row that bears on {@code axes} said where it was at all of them.
         *
         * <p>Only then does a class or a combination nothing sits in mean nothing reaches it. One row
         * that could not be placed at one of the positions leaves every class of that position, and
         * every combination it takes part in, undecided rather than untried.
         */
        MeasurementStatus status(List<Axis> axes) {
            if (someRowsUnseen) {
                return MeasurementStatus.PARTIAL;
            }
            for (Axis axis : axes) {
                if (couldNotSay(axis) > 0) {
                    return MeasurementStatus.PARTIAL;
                }
            }
            return MeasurementStatus.COMPLETE;
        }
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
    private static PartitionEvidence.PairSpace pairsOf(List<Axis> axes, Readings readings) {
        // The product of what a row can be written at, not of what the types declare. A class the
        // body rules out takes a whole slice of the product with it — every combination it takes part
        // in is one no row can sit in — which is a different thing from a pair whose two classes each
        // have rows but never together.
        long total = 0;
        for (int i = 0; i < axes.size(); i++) {
            for (int j = i + 1; j < axes.size(); j++) {
                total += (long) axes.get(i).eligible().size() * axes.get(j).eligible().size();
            }
        }
        if (total == 0) {
            return PartitionEvidence.PairSpace.NONE;
        }
        // Before the size of the space is worth mentioning. A combination nothing tried to sit in is
        // not a combination left untried by anybody, and how many of them there are says nothing
        // about a behavior no row names.
        if (readings.noRows() && !readings.someRowsUnseen()) {
            return PartitionEvidence.PairSpace.unavailable((int) Math.min(total, Integer.MAX_VALUE),
                    PartitionEvidence.PairSpace.Reason.NO_ROWS);
        }
        if (total > PAIR_LIMIT) {
            return new PartitionEvidence.PairSpace((int) Math.min(total, Integer.MAX_VALUE), 0, 0, 0,
                    (int) Math.min(total, Integer.MAX_VALUE), true, MeasurementStatus.PARTIAL, null);
        }
        Set<String> covered = new LinkedHashSet<>();
        for (Map<AxisId, Classification> where : readings.byRow()) {
            for (int i = 0; i < axes.size(); i++) {
                for (int j = i + 1; j < axes.size(); j++) {
                    String left = Readings.classIn(where, axes.get(i));
                    String right = Readings.classIn(where, axes.get(j));
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
                (int) total - reached, false, readings.status(axes), null);
    }

    private static PartitionEvidence.AxisCoverage coverageOf(Axis axis, Readings readings,
                                                             Exclusions excluded) {
        List<String> classes = axis.eligible().stream().map(PartitionClass::id).toList();
        // The model's own words for why, carried through so a report can say what it took out of the
        // denominator rather than showing a position with fewer classes than its type has. Said
        // whether or not a row was written: what the body rules out is a fact about the body.
        List<PartitionEvidence.ExcludedClass> ruled = excluded.at(axis.path()).stream()
                .filter(each -> axis.excluded().contains(each.name()))
                .map(each -> new PartitionEvidence.ExcludedClass(each.name(),
                        excluded.reasonsFor(axis.path(), each)))
                .toList();
        if (readings.noRows() && !readings.someRowsUnseen()) {
            return PartitionEvidence.AxisCoverage.unavailable(axis.id().toString(),
                    axis.path().toString(), classes, ruled,
                    PartitionEvidence.AxisCoverage.Reason.NO_ROWS);
        }
        Set<String> covered = new LinkedHashSet<>();
        for (Map<AxisId, Classification> where : readings.byRow()) {
            String in = Readings.classIn(where, axis);
            if (in != null && !axis.excluded().contains(in)) {
                covered.add(in);
            }
        }
        return new PartitionEvidence.AxisCoverage(axis.id().toString(), axis.path().toString(),
                classes, covered, ruled, readings.couldNotSay(axis),
                readings.status(List.of(axis)), null);
    }

    /**
     * A way to find out whether a value can be built at a boundary, or nothing where there is nothing
     * to build against.
     *
     * <p>The decoder a row's own fixture goes through, reached through the generator. It is the only
     * thing in the compiler that can answer the question — an invariant relating two fields refuses a
     * pair each field would have accepted alone — and it answers it one way: what it builds is a
     * witness, and what it refuses is a refusal of the candidates it tried.
     */
    @FunctionalInterface
    interface Probe {

        /** What building a row at this boundary came to, or null where the attempt could not be made
         * at all — which leaves the edge unknown rather than refused. */
        souther.compiler.partition.Generator.BoundaryAttempt attempt(BoundaryObligation obligation);
    }

    /**
     * Everything known about each line one position's rules drew.
     *
     * <p>The one place either question about a boundary is answered. Whether a row sits at it is read
     * off this compilation's rows; whether a row could sit at it is settled by the projection where
     * that read every rule, and by building a value where it did not. Both used to be worked out twice
     * — once for the report and once for the rows the generator offers — under rules that did not
     * quite agree, so a line the report called undecided was one the generator handed to an author
     * anyway.
     *
     * <p>An invariant's bound is met by writing the value: outside it nothing can be constructed, so
     * the value is the whole of what there is to reach. A guard's is not — the comparison has to have
     * been evaluated, and a row can carry the exact value and never reach the guard that cares about
     * it because an earlier branch went the other way. Nothing measures that until the arms are
     * instrumented, so a guard's boundary is unmeasured rather than met or missed.
     *
     * @param armsAsked whether the build asked for the arms at all. Whether the run then managed to
     *                  read them is a second question, and {@code observed} answers it — the two fail
     *                  differently and a measure that took one boolean for both could not say which
     *                  had happened.
     * @param probe     null where the module's classes or the runtime are not there to build against
     */
    static List<BoundaryAssessment> assess(
            Axis axis, List<String> parameters, souther.compiler.query.Adequacy.Observed observed,
            Symbols symbols, boolean armsAsked, boolean knownWritable, Probe probe,
            souther.compiler.numeric.NumericDomain.Bounds within) {
        List<RowOutcome> rows = observed.rows();
        List<BoundaryAssessment> out = new ArrayList<>();
        for (BoundaryObligation each : Partitions.obligationsOf(axis, symbols, within)) {
            BoundaryAssessment.Coverage coverage =
                    coverageOf(each, axis, parameters, observed, armsAsked);
            BoundaryAssessment.Attempt attempt = attemptAt(each, coverage, probe);
            out.add(new BoundaryAssessment(each, coverage,
                    writabilityOf(coverage, knownWritable, attempt), attempt));
        }
        return out;
    }

    /**
     * What building a row at this boundary came to, where one was worth building.
     *
     * <p>Nothing is built where nothing is owed: a boundary a row already sits at needs no candidate,
     * and one whose measurement never happened is not a piece of work to hand to anybody. Where a
     * candidate was worth building and there was nothing to build against, that is said as well —
     * it is a fact about the run, and reading it as a fact about the value is how "the classpath is
     * short of a jar" would become "this edge may not be writable".
     */
    private static BoundaryAssessment.Attempt attemptAt(BoundaryObligation obligation,
                                                        BoundaryAssessment.Coverage coverage,
                                                        Probe probe) {
        if (coverage instanceof BoundaryAssessment.Coverage.Hit) {
            return new BoundaryAssessment.Attempt.NotAttempted(
                    BoundaryAssessment.Attempt.Reason.A_ROW_IS_ALREADY_THERE);
        }
        if (!worthBuilding(coverage)) {
            return new BoundaryAssessment.Attempt.NotAttempted(
                    BoundaryAssessment.Attempt.Reason.NOT_MEASURED);
        }
        if (probe == null) {
            return new BoundaryAssessment.Attempt.NotAttempted(
                    BoundaryAssessment.Attempt.Reason.NO_CLASSES);
        }
        souther.compiler.partition.Generator.BoundaryAttempt made = probe.attempt(obligation);
        return switch (made) {
            case null -> new BoundaryAssessment.Attempt.NotAttempted(
                    BoundaryAssessment.Attempt.Reason.LINKAGE_FAILED);
            case souther.compiler.partition.Generator.BoundaryAttempt.Built built ->
                    new BoundaryAssessment.Attempt.Built(built.row());
            case souther.compiler.partition.Generator.BoundaryAttempt.Unresolved left ->
                    new BoundaryAssessment.Attempt.Unresolved(left.why());
        };
    }

    /** Whether a row sits at one boundary, and whether that could be told. */
    private static BoundaryAssessment.Coverage coverageOf(
            BoundaryObligation obligation, Axis axis, List<String> parameters,
            souther.compiler.query.Adequacy.Observed observed, boolean armsAsked) {
        List<RowOutcome> rows = observed.rows();
        boolean guard = obligation.origin() instanceof OriginRef.GuardOrigin;
        BoundaryAssessment.Coverage.Reason absent = guard
                ? whyNoGuardLine(rows, armsAsked, observed.armsUnseen(), observed.someRowsUnseen())
                : whyNoInvariantLine(rows, observed.someRowsUnseen());
        if (absent != null) {
            return new BoundaryAssessment.Coverage.NotMeasured(absent);
        }
        Met met = guard
                ? evaluatedAt(axis, parameters, rows, obligation.value(),
                        (OriginRef.GuardOrigin) obligation.origin())
                : writtenAt(axis, parameters, rows, obligation.value());
        if (met == Met.YES) {
            return new BoundaryAssessment.Coverage.Hit();
        }
        if (met == Met.UNREADABLE) {
            return new BoundaryAssessment.Coverage.Undecided();
        }
        // A row nothing read may be the row that is at this value. Found is still found — one row at
        // the boundary settles it whatever else went unread — but not-found is not settled.
        if (observed.someRowsUnseen()) {
            return new BoundaryAssessment.Coverage.Undecided();
        }
        // Nor is a hit that could not be looked for: a row that never finished left no hits, and a
        // guard's line is met by going through the comparison.
        if (guard && rows.stream().anyMatch(
                row -> row.disposition() == souther.compiler.observe.Disposition.INCOMPLETE)) {
            return new BoundaryAssessment.Coverage.Undecided();
        }
        return new BoundaryAssessment.Coverage.Missed();
    }

    /**
     * What says a row can be written at one boundary: the verdict, over the evidence there is.
     *
     * <p>The strongest evidence already in hand first. A row at the value went through the decoder,
     * which is the whole of what writable means, and costs nothing to read. Then the value that was
     * built, which went through the same decoder. Then the projection, which stands behind both rather
     * than in front of them: where it read every rule it proves the edge inhabited whatever the search
     * made of the particular candidates it tried.
     *
     * <p>Only the verdict is decided here. What was tried and what came of it is the attempt's to
     * say, and it is kept whether or not it changed this answer — an edge the projection proves is one
     * a search can still fail to reach, and a reader that had only this could not tell that it had.
     */
    private static BoundaryAssessment.Writability writabilityOf(
            BoundaryAssessment.Coverage coverage, boolean knownWritable,
            BoundaryAssessment.Attempt attempt) {
        if (coverage instanceof BoundaryAssessment.Coverage.Hit) {
            return new BoundaryAssessment.Writability.WitnessedByRow();
        }
        if (attempt instanceof BoundaryAssessment.Attempt.Built) {
            return new BoundaryAssessment.Writability.WitnessedByConstruction();
        }
        // A refusal and an attempt nobody made leave the same verdict, and a projection that read
        // every rule proves what neither of them found. Which is where the asymmetry lives: nothing
        // a search does can take a proof away, because nothing a search does is evidence against.
        return knownWritable ? new BoundaryAssessment.Writability.ProvenByProjection()
                : new BoundaryAssessment.Writability.Unknown();
    }

    /**
     * Whether a candidate is worth building for this boundary.
     *
     * <p>A line nothing measured is not a line an author is behind on. Where the arms were not asked
     * for, a guard's line has no answer at all, and where a row went unread the row that is at this
     * value may be one of the rows nothing saw — building a candidate for either hands somebody a
     * specific piece of work that may already be done.
     */
    private static boolean worthBuilding(BoundaryAssessment.Coverage coverage) {
        return coverage instanceof BoundaryAssessment.Coverage.Missed
                || (coverage instanceof BoundaryAssessment.Coverage.NotMeasured absent
                        && absent.reason() == BoundaryAssessment.Coverage.Reason.NO_ROWS);
    }

    /**
     * The first gate a {@code guard}'s line did not get through.
     *
     * <p>Its own path, because a guard's line and an invariant's are not measured the same way and so
     * cannot fail to be measured for the same reasons. Meeting this one takes the comparison having
     * run, which puts the arms in front of the rows: nothing a row carries decides it until the
     * classes that record where the row went exist and survived.
     */
    private static BoundaryAssessment.Coverage.Reason whyNoGuardLine(
            List<RowOutcome> rows, boolean armsAsked, boolean armsUnseen, boolean someRowsUnseen) {
        if (!armsAsked) {
            return BoundaryAssessment.Coverage.Reason.ARMS_NOT_ASKED;
        }
        if (armsUnseen) {
            return BoundaryAssessment.Coverage.Reason.ARMS_UNREADABLE;
        }
        return whyNoInvariantLine(rows, someRowsUnseen);
    }

    /**
     * The first gate an invariant's line did not get through.
     *
     * <p>Only the one: nothing outside the bound can be constructed, so writing the value is the whole
     * of what there is to reach and no instrumentation is owed. This is why the two origins are asked
     * separately — an invariant's line can never be waiting on the arms, and a measure that could say
     * so would be able to say something that is not true of it.
     */
    private static BoundaryAssessment.Coverage.Reason whyNoInvariantLine(
            List<RowOutcome> rows, boolean someRowsUnseen) {
        // Nothing read is not the same as nothing written. A source that could not be evaluated may
        // hold the row that is at this line, so the question is undecided rather than unasked, and
        // the reading below settles it that way.
        return rows.isEmpty() && !someRowsUnseen
                ? BoundaryAssessment.Coverage.Reason.NO_ROWS : null;
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

    /**
     * Whether an observation says what number was at this position.
     *
     * <p>Asked of the number rather than of the shape, because a boundary is only ever on a numeric
     * position and the truncation can be one layer in. A newtype is observed as a construction holding
     * its value, and a limit reached inside it leaves the construction readable with a truncation
     * where the number should be — which, read by shape, is a value that is simply not the boundary.
     */
    private static boolean readable(ObservedValue at) {
        return numberOf(at) != null;
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

    private Coverages() {}
}
