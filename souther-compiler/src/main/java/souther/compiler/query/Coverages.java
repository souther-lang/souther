package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Place;
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
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.Exclusions;
import souther.compiler.partition.GuardThresholds;
import souther.compiler.partition.NumericTerm;
import souther.compiler.partition.OriginRef;
import souther.compiler.partition.PartitionClass;
import souther.compiler.partition.Partitions;
import souther.compiler.partition.RowClasses;

import java.util.ArrayList;
import java.util.LinkedHashMap;
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
        GuardThresholds.Guards guards =
                GuardThresholds.of(behavior.name(), body, plan, parameters, symbols);
        return Partitions.withThresholds(partitioning, guards.thresholds(), symbols,
                guards.unread(), guards.singled(), guards.between());
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

        List<Axis> divided = new ArrayList<>();
        Readings readings = Readings.of(rows, parameters, partitioning.axes(),
                observed.someRowsUnseen());
        for (Axis axis : partitioning.axes()) {
            if (!axis.measurable()) {
                continue;   // said by `undivided`, which also says which kind of nothing it is
            }
            if (axis.derivable()) {
                axes.add(coverageOf(axis, readings, excluded));
                divided.add(axis);
            }
        }
        return new PartitionEvidence(PartitionEvidence.Partitioned.of(axes),
                PartitionEvidence.Bounded.of(boundaries), pairsOf(divided, readings),
                partitioning.undivided(), partitioning.unread(), partitioning.omitted(),
                whyUnclassified(readings.byRow(),
                        partitioning.axes().stream().map(Axis::id).toList()));
    }

    /**
     * Why the rows that could not be placed could not be placed — one reason per kind per position.
     *
     * <p>Not one per row. A hundred rows too large at the same position are one thing to say about
     * that position, and how many there were is the axis's count. Carrying the number here as well
     * would be the same fact under two names, and the two would be read side by side.
     *
     * <p>Walked in the order of {@code order} rather than of a row's own map, which is built with
     * {@code Map.copyOf} and so iterates in an order that changes between runs. A report that
     * changes between runs cannot be compared between runs.
     */
    static List<Incompleteness> whyUnclassified(List<Map<AxisId, Classification>> byRow,
                                                List<AxisId> order) {
        Map<Object, Incompleteness> byKind = new LinkedHashMap<>();
        for (Map<AxisId, Classification> where : byRow) {
            for (AxisId axis : order) {
                if (where.get(axis) instanceof Classification.Unclassified could) {
                    byKind.putIfAbsent(could.reason().identity(), could.reason());
                }
            }
        }
        return List.copyOf(byKind.values());
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
                    axis.term().toString(), classes, ruled,
                    PartitionEvidence.AxisCoverage.Reason.NO_ROWS);
        }
        Set<String> covered = new LinkedHashSet<>();
        for (Map<AxisId, Classification> where : readings.byRow()) {
            String in = Readings.classIn(where, axis);
            if (in != null && !axis.excluded().contains(in)) {
                covered.add(in);
            }
        }
        return new PartitionEvidence.AxisCoverage(axis.id().toString(), axis.term().toString(),
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
    interface Probe {

        /** What building a row at this boundary came to, or null where the attempt could not be made
         * at all — which leaves the edge unknown rather than refused. */
        souther.compiler.partition.Generator.BoundaryAttempt attempt(BoundaryObligation obligation);

        /** The same for a line between two positions, which is not at a count of its own: the count
         * to write at both of them is the rules' answer about the pair and is handed in. */
        souther.compiler.partition.Generator.BoundaryAttempt attemptBetween(
                BoundaryTarget.EqualTerms line, Place at);
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
        // Keyed by the line rather than by the reading of it. A guard inside a non-recursive helper
        // is read once per call of that helper, and the rows do not owe the same edge twice for
        // having been offered it twice; what each reading saw is merged below.
        java.util.SequencedMap<Line, BoundaryAssessment> out = new java.util.LinkedHashMap<>();
        for (BoundaryObligation each : Partitions.obligationsOf(axis, symbols, within)) {
            BoundaryAssessment.Coverage coverage =
                    coverageOf(each, axis, parameters, symbols, observed, armsAsked);
            BoundaryAssessment.Attempt attempt = attemptAt(each, coverage, probe);
            BoundaryAssessment made = new BoundaryAssessment(each, coverage,
                    writabilityOf(coverage, knownWritable, attempt), attempt);
            out.merge(new Line(each.side(), each.target(), each.origin().line()), made,
                    Coverages::whicheverSawMore);
        }
        return List.copyOf(out.values());
    }

    /** One line, told from another by where it is, what drew it and where that was — and not by which
     * copy of the body the reading came off. */
    private record Line(BoundaryObligation.BoundarySide side, BoundaryTarget at,
                        OriginRef.Line drawn) {}

    /**
     * Which of two readings of one line the report keeps.
     *
     * <p>Existential, the same way an arm is: a row met the edge if it met it through any reading of
     * it. So a reading that found a row outranks one that could not tell, which outranks one that
     * looked and found none, which outranks one that was never made. Anything else would let a
     * second call site of a helper take back what a row at the first one established.
     */
    private static BoundaryAssessment whicheverSawMore(BoundaryAssessment a, BoundaryAssessment b) {
        return rank(b.coverage()) > rank(a.coverage()) ? b : a;
    }

    private static int rank(BoundaryAssessment.Coverage coverage) {
        return switch (coverage) {
            case BoundaryAssessment.Coverage.Hit _ -> 3;
            case BoundaryAssessment.Coverage.Undecided _ -> 2;
            case BoundaryAssessment.Coverage.Missed _ -> 1;
            case BoundaryAssessment.Coverage.NotMeasured _ -> 0;
        };
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
            BoundaryObligation obligation, Axis axis, List<String> parameters, Symbols symbols,
            souther.compiler.query.Adequacy.Observed observed, boolean armsAsked) {
        List<RowOutcome> rows = observed.rows();
        boolean guard = obligation.origin() instanceof OriginRef.GuardOrigin;
        BoundaryAssessment.Coverage.Reason absent = guard
                ? whyNoGuardLine(rows, armsAsked, observed.armsUnseen(), observed.someRowsUnseen())
                : whyNoInvariantLine(rows, observed.someRowsUnseen());
        if (absent != null) {
            return new BoundaryAssessment.Coverage.NotMeasured(absent);
        }
        Met met = switch (obligation.target()) {
            case BoundaryTarget.AtPlace place -> guard
                    ? evaluatedAt(axis, parameters, rows, symbols, place.at(),
                            (OriginRef.GuardOrigin) obligation.origin())
                    : writtenAt(axis, parameters, rows, symbols, place.at());
            case BoundaryTarget.EqualTerms line ->
                    heldBetween(line, parameters, rows,
                            (OriginRef.GuardOrigin) obligation.origin());
        };
        return verdictOf(met, guard, observed);
    }

    /**
     * What was established about each line a body draws between two of its positions.
     *
     * <p>Beside the lines an axis carries rather than among them. A line between two positions is on
     * neither of them, so there is no axis to hang it off — and a behavior can have one while having no
     * axis at all, which is every model whose inputs are plain numbers nothing bounds.
     *
     * <p>Nothing is promised of one yet. Whether a row can be written on the line takes a count both
     * positions admit, and until that is read the line is one nothing has shown to be writable — which
     * is reported and not counted, the same account any other unpromised edge gets.
     */
    static List<BoundaryAssessment> assessBetween(
            Partitions.Partitioning partitioning, List<String> parameters,
            souther.compiler.query.Adequacy.Observed observed, boolean armsAsked, Probe probe) {
        List<RowOutcome> rows = observed.rows();
        // Keyed by the line the author drew, the way a line at a place is. A guard inside a
        // non-recursive helper is read once per call of that helper, and the rows do not owe the same
        // line twice for having been offered it twice — nor may one reading of it take back what
        // another established.
        java.util.SequencedMap<Line, BoundaryAssessment> out = new LinkedHashMap<>();
        for (BoundaryObligation each : partitioning.between()) {
            BoundaryTarget.EqualTerms line = (BoundaryTarget.EqualTerms) each.target();
            BoundaryAssessment.Coverage.Reason absent =
                    whyNoGuardLine(rows, armsAsked, observed.armsUnseen(), observed.someRowsUnseen());
            BoundaryAssessment.Coverage coverage = absent != null
                    ? new BoundaryAssessment.Coverage.NotMeasured(absent)
                    : verdictOf(heldBetween(line, parameters, rows,
                            (OriginRef.GuardOrigin) each.origin()), true, observed);
            // A place both positions admit is what a row on the line writes. Read once: it is what a
            // candidate is built at, and what proves the line writable where the two are independent.
            Place at = Partitions.commonPlace(partitioning.domains(), line);
            BoundaryAssessment.Attempt attempt = attemptBetween(line, at, coverage, probe);
            out.merge(new Line(each.side(), each.target(), each.origin().line()),
                    new BoundaryAssessment(each, coverage,
                            writabilityOf(coverage, provenWritable(partitioning, line, at), attempt),
                            attempt),
                    Coverages::whicheverSawMore);
        }
        return List.copyOf(out.values());
    }

    /**
     * Whether the rules alone prove a row can be written on a line between two positions.
     *
     * <p>Two ranges overlapping is not two positions holding one value. A place in both is a place
     * each of them admits *on its own*, and a rule relating them can refuse the pair that each half
     * would have taken: under {@code data Pair = { a: Int, b: Int } invariant a < b} the ranges of
     * {@code a} and {@code b} overlap everywhere and the line {@code a = b} has no value at all.
     * Projecting a range and completing an assignment are two questions of one rule set, which is why
     * {@link souther.compiler.check.FieldDomains} asks the second with the first already settled.
     *
     * <p>So the projection proves this only where no rule can relate the two: two positions under
     * different parameters. A behavior's parameters are constructed one at a time and a model has no
     * way to write a rule across them, so a value each admits is a pair both admit. Under one
     * parameter that does not hold, and what settles the line there is a witness — a row already on
     * it, or a value the module's own decoder took, which is the one thing here that answers whether
     * a rule relating two fields accepts the pair.
     *
     * <p>Not a claim that such a line cannot be written. Nothing is counted for want of a proof, and
     * the line is reported as one nothing has promised — which is what any other unpromised edge gets.
     */
    private static boolean provenWritable(Partitions.Partitioning partitioning,
                                          BoundaryTarget.EqualTerms line, Place at) {
        boolean independent = !line.on().path().head().equals(line.against().path().head());
        return at != null && independent
                && partitioning.edgeIsKnownWritable(line.on())
                && partitioning.edgeIsKnownWritable(line.against());
    }

    /** What building a row on a line between two positions came to, where one was worth building. */
    private static BoundaryAssessment.Attempt attemptBetween(
            BoundaryTarget.EqualTerms line, Place at, BoundaryAssessment.Coverage coverage,
            Probe probe) {
        if (coverage instanceof BoundaryAssessment.Coverage.Hit) {
            return new BoundaryAssessment.Attempt.NotAttempted(
                    BoundaryAssessment.Attempt.Reason.A_ROW_IS_ALREADY_THERE);
        }
        if (!worthBuilding(coverage)) {
            return new BoundaryAssessment.Attempt.NotAttempted(
                    BoundaryAssessment.Attempt.Reason.NOT_MEASURED);
        }
        if (at == null) {
            // The rules leave the two positions no place in common. Said as the search coming to
            // nothing rather than as a search nobody ran: this is what was asked and what came back.
            return new BoundaryAssessment.Attempt.Unresolved(
                    new souther.compiler.partition.Generator.UnresolvedCombination(
                            List.of(line.left() + " = " + line.right()),
                            souther.compiler.partition.Generator.UnresolvedCombination.Reason
                                    .NOTHING_COMPOSES_ONE));
        }
        if (probe == null) {
            return new BoundaryAssessment.Attempt.NotAttempted(
                    BoundaryAssessment.Attempt.Reason.NO_CLASSES);
        }
        souther.compiler.partition.Generator.BoundaryAttempt made = probe.attemptBetween(line, at);
        return switch (made) {
            case null -> new BoundaryAssessment.Attempt.NotAttempted(
                    BoundaryAssessment.Attempt.Reason.LINKAGE_FAILED);
            case souther.compiler.partition.Generator.BoundaryAttempt.Built built ->
                    new BoundaryAssessment.Attempt.Built(built.row());
            case souther.compiler.partition.Generator.BoundaryAttempt.Unresolved left ->
                    new BoundaryAssessment.Attempt.Unresolved(left.why());
        };
    }

    /**
     * Whether a row is on a line where two terms hold one count.
     *
     * <p>Both sides through the term's own reader, which is the one that reaches a count through the
     * newtype a position may be written as. Compared as counts and not as observed values: the two
     * positions are of one carrier and need not be of one type — {@code Charge} against {@code Ceiling}
     * is what the domain this was found in is made of — and two values of different types are never
     * equal however much the numbers inside them agree.
     */
    private static Met heldBetween(BoundaryTarget.EqualTerms line, List<String> parameters,
                                   List<RowOutcome> rows, OriginRef.GuardOrigin origin) {
        boolean unreadable = false;
        for (RowOutcome row : rows) {
            NumericTerm.Reading on = line.on()
                    .read(RowClasses.valueAt(row, parameters, line.on().path()), line.carrier());
            NumericTerm.Reading against = line.against()
                    .read(RowClasses.valueAt(row, parameters, line.against().path()), line.carrier());
            if (on instanceof NumericTerm.Reading.Missing
                    || against instanceof NumericTerm.Reading.Missing) {
                unreadable = true;
                continue;
            }
            if (on instanceof NumericTerm.Reading.Number here
                    && against instanceof NumericTerm.Reading.Number there
                    && here.value().sameAs(there.value())
                    && row.hits().contains(origin.site())) {
                return Met.YES;
            }
        }
        return unreadable ? Met.UNREADABLE : Met.NO;
    }

    /** What a reading of the rows comes to, once what could not be read is accounted for. */
    private static BoundaryAssessment.Coverage verdictOf(
            Met met, boolean guard, souther.compiler.query.Adequacy.Observed observed) {
        List<RowOutcome> rows = observed.rows();
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
     * Whether a row wrote the boundary value <em>and</em> got the comparison that cares about it to
     * produce a value.
     *
     * <p>Both, because either alone is a different claim. A row can hand a behavior exactly 100000 and
     * take an earlier branch that never reaches {@code cost <= 100000}, and counting that as having
     * tried the boundary would report a rule as exercised that nothing has run.
     *
     * <p>Asked of the comparison's own site and of no arm. A condition stops as soon as its answer is
     * settled, so which arm a row landed in is not an answer about which of the condition's
     * comparisons ran: under {@code A && B} the arm the condition failed on holds the rows that made
     * {@code B} false and the rows that never reached {@code B}. Reading the arms here credited the
     * second kind and could not credit the first.
     */
    private static Met evaluatedAt(Axis axis, List<String> parameters, List<RowOutcome> rows,
                                   Symbols symbols, Place boundary,
                                   OriginRef.GuardOrigin origin) {
        boolean unreadable = false;
        for (RowOutcome row : rows) {
            switch (readingFor(axis, parameters, symbols, row)) {
                case NumericTerm.Reading.Missing _ -> unreadable = true;
                case NumericTerm.Reading.NotNumber _ -> { }
                case NumericTerm.Reading.Number number -> {
                    if (number.value().sameAs(boundary)
                            && row.hits().contains(origin.site())) {
                        return Met.YES;
                    }
                }
            }
        }
        return unreadable ? Met.UNREADABLE : Met.NO;
    }

    private static Met writtenAt(Axis axis, List<String> parameters, List<RowOutcome> rows,
                                 Symbols symbols, Place boundary) {
        boolean unreadable = false;
        for (RowOutcome row : rows) {
            switch (readingFor(axis, parameters, symbols, row)) {
                case NumericTerm.Reading.Missing _ -> unreadable = true;
                case NumericTerm.Reading.NotNumber _ -> { }
                case NumericTerm.Reading.Number number -> {
                    if (number.value().sameAs(boundary)) {
                        return Met.YES;
                    }
                }
            }
        }
        return unreadable ? Met.UNREADABLE : Met.NO;
    }

    /**
     * What this row put on the line's own term, kept as the three answers it is.
     *
     * <p>Asked of the term and not of the shape of what sits at the position. A boundary is on a
     * number, and which number a value carries is the term's to say: the content of a location where
     * the line is on that, and how long the string is where it is on that. Read as "is this
     * observation a number", a string was unreadable at every position and every length boundary was
     * undecided for every row.
     *
     * <p>The three are kept apart here rather than folded into a number-or-null. An observation the
     * run could not read leaves this line undecided, because the row that was cut short may be the
     * row at the value. A value that was read and is not a number of this term does not: it is a row
     * that is not at this boundary, and calling it undecided would report a term that does not fit
     * its position as a row nobody could read — which is the answer {@code Intervals} already gives
     * a class asked the same question, and it has to be the same answer.
     */
    private static NumericTerm.Reading readingFor(Axis axis, List<String> parameters,
                                                  Symbols symbols, RowOutcome row) {
        return axis.term().read(RowClasses.valueAt(row, parameters, axis.path()),
                axis.term().carrierAt(axis.type(), symbols));
    }

    private Coverages() {}
}
