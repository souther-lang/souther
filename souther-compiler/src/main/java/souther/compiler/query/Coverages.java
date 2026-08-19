package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.PathReachability;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Place;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.observe.Counting;
import souther.compiler.observe.RowOutcome;
import souther.compiler.partition.Axis;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.Border;
import souther.compiler.partition.Criterion;
import souther.compiler.partition.Demand;
import souther.compiler.partition.Generator;
import souther.compiler.partition.PointRole;
import souther.compiler.partition.Region;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.inputs.InputDomain;
import souther.compiler.partition.EnsuresThresholds;
import souther.compiler.partition.GuardThresholds;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.partition.BoundaryLine;
import souther.compiler.partition.PartitionClass;
import souther.compiler.partition.Partitions;
import souther.compiler.partition.BehaviorInputs;
import souther.compiler.partition.RowClasses;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
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
    static Partitions.Partitioning partitioningOf(Hir.SpecBehavior behavior, InputDomain inputs,
                                                  Sig sig, Symbols symbols,
                                                  Core body, CoverageSites.Plan plan,
                                                  PathReachability.Answers arrives,
                                                  souther.compiler.check.StatedContract stated) {
        List<String> parameters = behavior.params().stream().map(Hir.Param::name).toList();
        // What a row's values are, where they sit and what they are written as, read together:
        // a field under a name is reached by taking the name off, and a walk given the paths
        // alone reaches nothing where the derivation reaches a field.
        BehaviorInputs where = new BehaviorInputs(parameters, sig.inputTypes(), symbols);
        Partitions.Partitioning partitioning = Partitions.of(behavior.name(), inputs, symbols);
        // What the behavior states about its own answer, which is read whether or not anything
        // implements it: a clause is written against the declaration, so an injected behavior draws
        // its lines like any other and there is no body for them to have come out of.
        EnsuresThresholds.Clauses clauses = EnsuresThresholds.of(stated, inputs, symbols);
        GuardThresholds.Guards guards = body == null ? GuardThresholds.Guards.NONE
                : GuardThresholds.of(behavior.name(), body, plan, inputs, symbols);
        // Both producers of one kind of line, put together before the position is divided. Two
        // rules at one value are one cut and stay separate obligations, which is what the merge
        // below does — applied one producer at a time, a clause and a guard naming one number would
        // divide the position twice.
        return Partitions.withThresholds(partitioning,
                both(clauses.thresholds(), guards.thresholds()), symbols,
                both(clauses.unread(), guards.unread()),
                both(clauses.singled(), guards.singled()),
                both(clauses.between(), guards.between()), arrives);
    }

    /** The two producers' lines, in one list. */
    private static <T> List<T> both(List<T> declared, List<T> compared) {
        if (declared.isEmpty()) {
            return compared;
        }
        List<T> all = new ArrayList<>(declared);
        all.addAll(compared);
        return List.copyOf(all);
    }

    /**
     * @param boundaries what was established about every line this behavior's rules drew, made once
     *                   by {@link souther.compiler.query.Adequacy.Boundaries} and read here. Measuring
     *                   a line takes putting a value through the module's decoders, which is not
     *                   something a coverage count can do on its own and not something that should
     *                   happen twice.
     */
    static PartitionEvidence of(Hir.SpecBehavior behavior, InputDomain inputs, Sig sig,
                                Symbols symbols, Core body,
                                CoverageSites.Plan plan, souther.compiler.query.Adequacy.Observed observed,
                                List<BorderAssessment> boundaries,
                                PathReachability.Answers arrives,
                                souther.compiler.check.StatedContract stated) {
        List<RowOutcome> rows = observed.rows();
        List<String> parameters = behavior.params().stream().map(Hir.Param::name).toList();
        // What a row's values are, where they sit and what they are written as, read together:
        // a field under a name is reached by taking the name off, and a walk given the paths
        // alone reaches nothing where the derivation reaches a field.
        BehaviorInputs where = new BehaviorInputs(parameters, sig.inputTypes(), symbols);
        Partitions.Partitioning partitioning =
                partitioningOf(behavior, inputs, sig, symbols, body, plan, arrives, stated);

        List<PartitionEvidence.AxisCoverage> axes = new ArrayList<>();

        List<Axis> divided = new ArrayList<>();
        Readings readings = Readings.of(rows, where, partitioning.axes(),
                observed.someRowsUnseen());
        for (Axis axis : partitioning.axes()) {
            if (!axis.measurable()) {
                continue;   // said by `undivided`, which also says which kind of nothing it is
            }
            if (axis.derivable()) {
                axes.add(coverageOf(axis, readings));
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

        static Readings of(List<RowOutcome> rows, BehaviorInputs where, List<Axis> axes,
                           boolean someRowsUnseen) {
            List<Map<AxisId, Classification>> read = new ArrayList<>();
            for (RowOutcome row : rows) {
                read.add(RowClasses.of(row, where, axes));
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
        // The product of what a row can be written at, not of what the types declare. A case the
        // rules refuse is not a class of its position at all, so the slice of the product it would
        // have taken part in is not here to be counted — which is a different thing from a pair
        // whose two classes each have rows but never together.
        long total = 0;
        for (int i = 0; i < axes.size(); i++) {
            for (int j = i + 1; j < axes.size(); j++) {
                total += (long) axes.get(i).classes().size() * axes.get(j).classes().size();
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

    private static PartitionEvidence.AxisCoverage coverageOf(Axis axis, Readings readings) {
        List<String> classes = axis.classes().stream().map(PartitionClass::id).toList();
        // What the axis already says about which of this position's rules nothing accounted for,
        // each named. Read off the axis rather than worked out here, and in the questions' own
        // words: the vocabulary beside it says why a division could not be derived, which is a
        // different question, and borrowing it left a reader with a sentence that named neither
        // (issue #842).
        PartitionEvidence.AxisCoverage.Reading read = new PartitionEvidence.AxisCoverage.Reading(
                axis.rulesNotReached()
                        ? PartitionEvidence.AxisCoverage.Reach.SOME_OUT_OF_SIGHT
                        : PartitionEvidence.AxisCoverage.Reach.EVERY_RULE,
                // What the axis already says about which of this position's rules nothing accounted
                // for, each named. Read off the axis rather than worked out here, and in the
                // questions' own words: the vocabulary beside it says why a division could not be
                // derived, which is a different question, and borrowing it left a reader with a
                // sentence that named neither (issue #842).
                axis.unanswered().stream()
                        .map(each -> {
                            // The subject the question carries, resolved against the axis it is at.
                            // A question about the position is spelled as the position and one
                            // about a number taken of it as the term, and which of the two it is
                            // was settled where the question was raised — not here, and not by
                            // whatever a renderer has to hand.
                            String subject = each.owed().subject().measured()
                                    ? axis.term().toString() : axis.path().toString();
                            return new PartitionEvidence.AxisCoverage.Unanswered(
                                    each.rule().named(), each.owed().obligation(), subject);
                        })
                        .toList());
        // Nothing a body claims is in scope here. What a row is owed at is counted first and on its
        // own, and what was declared about those positions is put beside it afterwards
        // ({@link ClaimReport}) — which is what keeps a claim from narrowing a denominator by being
        // in reach of the code that counts one.
        if (readings.noRows() && !readings.someRowsUnseen()) {
            return PartitionEvidence.AxisCoverage.unavailable(axis.id().toString(),
                    axis.term().toString(), classes,
                    PartitionEvidence.AxisCoverage.Reason.NO_ROWS, read);
        }
        Set<String> covered = new LinkedHashSet<>();
        for (Map<AxisId, Classification> where : readings.byRow()) {
            String in = Readings.classIn(where, axis);
            if (in != null) {
                covered.add(in);
            }
        }
        return new PartitionEvidence.AxisCoverage(axis.id().toString(), axis.term().toString(),
                classes, covered, readings.couldNotSay(axis), readings.status(List.of(axis)), null,
                read);
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

        /** What building a row at this place came to, or null where the attempt could not be made
         * at all — which leaves the point unknown rather than refused. */
        souther.compiler.partition.Generator.BoundaryAttempt attempt(BoundaryTarget.AtPlace at);

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
    static List<BorderAssessment> assess(
            Axis axis, BehaviorInputs where, souther.compiler.query.Adequacy.Observed observed,
            boolean armsAsked, boolean knownWritable, Probe probe,
            souther.compiler.numeric.NumericDomain.Bounds within) {
        // Keyed by the line rather than by the reading of it. A guard inside a non-recursive helper
        // is read once per call of that helper, and the rows do not owe the same border twice for
        // having been offered it twice; what each reading saw is merged below.
        java.util.SequencedMap<BoundaryLine, BorderAssessment> out = new java.util.LinkedHashMap<>();
        for (Border each : Partitions.bordersOf(axis, where.symbols(), within)) {
            out.merge(BoundaryLine.of(each),
                    assessedAt(each, axis, where, observed, armsAsked, knownWritable, probe, within),
                    Coverages::whicheverSawMore);
        }
        return List.copyOf(out.values());
    }

    /**
     * What each of one border's four points came to.
     *
     * <p>Every role, and the ones nobody is owed a row in carry the border's own reason rather than
     * being left out. What a row has to do is the criterion's ({@link Criterion}); what it has to do
     * <em>beyond</em> that is the border's — a line a fork of a body drew is met by getting the
     * comparison to answer as well as by writing the value, and that holds of all four of its points.
     * Read off the role instead, an {@code IN} point of a guard would be met by a row that never
     * reached the guard.
     */
    private static BorderAssessment assessedAt(
            Border border, Axis axis, BehaviorInputs where,
            souther.compiler.query.Adequacy.Observed observed, boolean armsAsked,
            boolean knownWritable, Probe probe,
            souther.compiler.numeric.NumericDomain.Bounds within) {
        java.util.EnumMap<PointRole, ItemAssessment> items = new java.util.EnumMap<>(PointRole.class);
        for (PointRole role : PointRole.values()) {
            items.put(role, switch (border.demand(role)) {
                case Demand.NotOwed not -> new ItemAssessment.NotOwed(not.reason());
                case Demand.Owed owed -> {
                    ItemAssessment.Coverage coverage = coverageAt(owed.criterion(), border, axis,
                            where, observed, armsAsked);
                    ItemAssessment.Attempt attempt =
                            attemptAt(owed.criterion(), border, coverage, probe, within);
                    yield new ItemAssessment.Owed(owed.criterion(), coverage,
                            writabilityOf(coverage, knownWritable, attempt), attempt);
                }
            });
        }
        return new BorderAssessment(border, items);
    }

    /**
     * Which of two readings of one line the report keeps.
     *
     * <p>Existential and per point, the same way an arm is: a row met a point if it met it through
     * any reading of the line. So a reading that found a row outranks one that could not tell, which
     * outranks one that looked and found none, which outranks one that was never made. Anything else
     * would let a second call site of a helper take back what a row at the first one established.
     *
     * <p>Point by point rather than border by border. Two readings of one line are the same border
     * and can have seen different things at different points, and keeping whichever border saw more
     * on the whole would throw away a point the other one had.
     */
    private static BorderAssessment whicheverSawMore(BorderAssessment a, BorderAssessment b) {
        java.util.EnumMap<PointRole, ItemAssessment> kept = new java.util.EnumMap<>(PointRole.class);
        for (PointRole role : PointRole.values()) {
            kept.put(role, rank(b.at(role)) > rank(a.at(role)) ? b.at(role) : a.at(role));
        }
        return new BorderAssessment(a.border(), kept);
    }

    private static int rank(ItemAssessment item) {
        if (!(item instanceof ItemAssessment.Owed owed)) {
            // Two readings of one line owe the same points, so this is one of them against itself.
            return 0;
        }
        return switch (owed.coverage()) {
            case ItemAssessment.Coverage.Hit _ -> 3;
            case ItemAssessment.Coverage.Undecided _ -> 2;
            case ItemAssessment.Coverage.Missed _ -> 1;
            case ItemAssessment.Coverage.NotMeasured _ -> 0;
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
    private static ItemAssessment.Attempt attemptAt(
            Criterion criterion, Border border, ItemAssessment.Coverage coverage, Probe probe,
            souther.compiler.numeric.NumericDomain.Bounds within) {
        return whereOneIsWorthBuilding(coverage, () -> {
            if (probe == null) {
                return new ItemAssessment.Attempt.NotAttempted(
                        ItemAssessment.Attempt.Reason.NO_CLASSES);
            }
            // Which place to try is asked of the criterion, and a side answers with one it holds.
            // That value is a candidate to offer and no part of the item: another row in the same
            // side is at the point as much as this one would be.
            Place standing = souther.compiler.partition.Generator.placeFor(
                    criterion, border.cut().carrier(), within);
            if (standing == null) {
                // Nothing composed a value here. Said as a search that came to nothing rather than
                // as one nobody ran: this is what was asked and what came back.
                //
                // Named by the point and not by the line. A border's four points fail separately —
                // the row on the line can be composed while the side beside it holds nothing this
                // can write — and named by the line all four say the same words, which a reader
                // that prints each reason once shows as one.
                return nothingComposedOne(border.label(criterion));
            }
            return whatCameOfIt(probe.attempt(new BoundaryTarget.AtPlace(
                    ((BoundaryTarget.AtPlace) border.cut()).axis(), border.cut().carrier(),
                    standing)));
        });
    }

    /**
     * What was tried at one point, where anything was worth trying at all.
     *
     * <p>The two gates in one place because they are one rule and there are three searches. A point
     * a row already sits at needs no candidate, and one whose measurement never happened is not a
     * piece of work to hand to anybody — offered anyway, both put a specific row in front of an
     * author that may already be written. Written per search, the third one to be added skipped
     * them and said a search had run and failed at points nothing had looked at.
     */
    private static ItemAssessment.Attempt whereOneIsWorthBuilding(
            ItemAssessment.Coverage coverage,
            java.util.function.Supplier<ItemAssessment.Attempt> search) {
        if (coverage instanceof ItemAssessment.Coverage.Hit) {
            return new ItemAssessment.Attempt.NotAttempted(
                    ItemAssessment.Attempt.Reason.A_ROW_IS_ALREADY_THERE);
        }
        if (!worthBuilding(coverage)) {
            return new ItemAssessment.Attempt.NotAttempted(
                    ItemAssessment.Attempt.Reason.NOT_MEASURED);
        }
        return search.get();
    }

    /** A search that came to nothing at {@code subject}, which is what a point is written as. */
    private static ItemAssessment.Attempt nothingComposedOne(String subject) {
        return new ItemAssessment.Attempt.Unresolved(
                new souther.compiler.partition.Generator.UnresolvedCombination(List.of(subject),
                        souther.compiler.partition.Generator.UnresolvedCombination.Reason
                                .NOTHING_COMPOSES_ONE));
    }

    /** What a search of the module's own decoders came to, in this measure's words. */
    private static ItemAssessment.Attempt whatCameOfIt(
            souther.compiler.partition.Generator.BoundaryAttempt made) {
        return switch (made) {
            case null -> new ItemAssessment.Attempt.NotAttempted(
                    ItemAssessment.Attempt.Reason.LINKAGE_FAILED);
            case souther.compiler.partition.Generator.BoundaryAttempt.Built built ->
                    new ItemAssessment.Attempt.Built(built.row());
            case souther.compiler.partition.Generator.BoundaryAttempt.Unresolved left ->
                    new ItemAssessment.Attempt.Unresolved(left.why());
        };
    }

    /** Whether a row is at one point of a border, and whether that could be told. */
    private static ItemAssessment.Coverage coverageAt(
            Criterion criterion, Border border, Axis axis, BehaviorInputs where,
            souther.compiler.query.Adequacy.Observed observed, boolean armsAsked) {
        List<RowOutcome> rows = observed.rows();
        // Whether meeting this border takes the comparison having run, asked of the rule rather than
        // read off which kind it is, and asked once for the border rather than once per point. A
        // guard's line is about a place in a body and is reached or not; an invariant's and a
        // clause's are about the values — one refuses everything outside its bound, the other states
        // a relation — so for both of those writing the value is the whole of what there is to reach.
        java.util.OptionalInt site = border.origin().comparisonSite();
        boolean guard = site.isPresent();
        ItemAssessment.Coverage.Reason absent = guard
                ? whyNoGuardLine(rows, armsAsked, observed.armsUnseen(), observed.someRowsUnseen())
                : whyNoInvariantLine(rows, observed.someRowsUnseen());
        if (absent != null) {
            return new ItemAssessment.Coverage.NotMeasured(absent);
        }
        Met met = switch (border.cut()) {
            case BoundaryTarget.AtPlace _ -> metAt(axis, where, rows, holding(criterion), site);
            case BoundaryTarget.EqualTerms line -> metBetween(line, where, rows,
                    holdingBetween(criterion), site);
        };
        return verdictOf(met, guard, observed);
    }

    /**
     * What a row's place at this position has to be, for a border drawn at a place.
     *
     * <p>One predicate for both kinds of item, which is what keeps a side from being measured against
     * a value. A point names a place and is met by writing it; a side names a set and is met by
     * landing anywhere in it, and reading the second as the first would ask for whichever value a
     * search happened to compose.
     */
    private static java.util.function.Predicate<Place> holding(Criterion criterion) {
        return switch (criterion) {
            case Criterion.AtThePlace at -> place -> place.sameAs(at.place());
            case Criterion.InTheRegion side -> switch (side.region()) {
                case Region.Beyond beyond -> beyond::holds;
                case Region.AdmittedOtherThan other -> other::holds;
                // A pair of terms falling apart is not a place of one position. Reaching here is the
                // border and the criterion it built disagreeing about which shape the line has.
                case Region.TermsApart _ -> throw new IllegalStateException(
                        "a line at a place was given a criterion about two terms");
            };
            case Criterion.WhereTheTermsMeet _ -> throw new IllegalStateException(
                    "a line at a place was given a criterion about two terms");
        };
    }

    /** The same for a border between two positions, where the row writes two places. */
    private static java.util.function.BiPredicate<Place, Place> holdingBetween(
            Criterion criterion) {
        return switch (criterion) {
            case Criterion.WhereTheTermsMeet _ -> Place::sameAs;
            case Criterion.InTheRegion side when side.region() instanceof Region.TermsApart apart ->
                    apart::holds;
            case Criterion.InTheRegion _, Criterion.AtThePlace _ -> throw new IllegalStateException(
                    "a line between two positions was given a criterion about one place");
        };
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
    static List<BorderAssessment> assessBetween(
            Partitions.Partitioning partitioning, BehaviorInputs where,
            souther.compiler.query.Adequacy.Observed observed, boolean armsAsked, Probe probe) {
        // Keyed by the line the author drew, the way a line at a place is. A guard inside a
        // non-recursive helper is read once per call of that helper, and the rows do not owe the same
        // line twice for having been offered it twice — nor may one reading of it take back what
        // another established.
        java.util.SequencedMap<BoundaryLine, BorderAssessment> out = new LinkedHashMap<>();
        for (Border each : partitioning.between()) {
            BoundaryTarget.EqualTerms line = (BoundaryTarget.EqualTerms) each.cut();
            // A place both positions admit is what a row on the line writes. Read once: it is what a
            // candidate is built at, and what proves the line writable where the two are independent.
            Place at = Partitions.commonPlace(partitioning.domains(), line);
            java.util.EnumMap<PointRole, ItemAssessment> items =
                    new java.util.EnumMap<>(PointRole.class);
            for (PointRole role : PointRole.values()) {
                items.put(role, switch (each.demand(role)) {
                    case Demand.NotOwed not -> new ItemAssessment.NotOwed(not.reason());
                    // No axis: a line between two positions is on neither of them, and what a row
                    // wrote is read at both terms rather than at a position's own.
                    case Demand.Owed owed -> {
                        ItemAssessment.Coverage coverage = coverageAt(owed.criterion(), each, null,
                                where, observed, armsAsked);
                        // Only the row on the line is composed. A side of such a line is a set of
                        // pairs, and building a row where the two are equal would witness the point
                        // on the line as though it stood for the side beside it.
                        //
                        // Through the same gate as every other search, and that is the whole of why
                        // the gate is not written here. A point a row already sits at and a point
                        // nothing measured are not points a search comes back empty from; answered
                        // that way, `--generate` printed a reason at every side of every such line
                        // on every run.
                        ItemAssessment.Attempt attempt = whereOneIsWorthBuilding(coverage, () ->
                                owed.criterion() instanceof Criterion.WhereTheTermsMeet
                                        ? composedOnTheLine(line, at, probe)
                                        : nothingComposedOne(each.label(role)));
                        yield new ItemAssessment.Owed(owed.criterion(), coverage,
                                writabilityOf(coverage, false, attempt), attempt);
                    }
                });
            }
            out.merge(BoundaryLine.of(each), new BorderAssessment(each, items),
                    Coverages::whicheverSawMore);
        }
        return List.copyOf(out.values());
    }

    /**
     * Why a line between two positions is never counted on the strength of the rules alone.
     *
     * <p>Two ranges overlapping is not two positions holding one value. A place in both is one each of
     * them admits *on its own*, and what refuses the pair need not appear in either range: a rule
     * relating two fields of one record does not — under {@code invariant a < b} the two ranges run
     * over each other everywhere and the line {@code a = b} holds nothing — and neither does a rule
     * the ranges could not take in, since a range says nothing is missing where a disequality left a
     * hole and a pattern left one string.
     *
     * <p>Nor is "every rule was read" the question. That says the checker understood each clause, not
     * that each clause reached the ranges: {@code String.matches} is read and bounds nothing, so a
     * position admitting one string looks unbounded from here.
     *
     * <p>So the line is settled by a witness and by nothing else — a row already on it, or a value the
     * module's own decoder took, which is the one thing here that reads every rule of a value at once.
     * That is not a claim that a line without one cannot be written: it is reported as one nothing has
     * promised, which is the account any other unpromised edge gets, and a witness found later counts
     * it. A line at a place of one position keeps its own proof, where the rules that bound it are the
     * rules that drew it.
     */
    /** What building a row on a line between two positions came to, where one was worth building. */
    private static ItemAssessment.Attempt composedOnTheLine(BoundaryTarget.EqualTerms line,
                                                            Place at, Probe probe) {
        if (at == null) {
            // The rules leave the two positions no place in common. Said as the search coming to
            // nothing rather than as a search nobody ran: this is what was asked and what came back.
            return nothingComposedOne(line.left() + " = " + line.right());
        }
        if (probe == null) {
            return new ItemAssessment.Attempt.NotAttempted(
                    ItemAssessment.Attempt.Reason.NO_CLASSES);
        }
        return whatCameOfIt(probe.attemptBetween(line, at));
    }

    /**
     * Whether a row is on a line where two terms hold one count.
     *
     * <p>Both sides through the term's own reader, which is the one that reaches a count through the
     * newtype a position may be written as. Compared as counts and not as observed values: the two
     * positions are of one carrier and need not be of one type — {@code Charge} against {@code Ceiling}
     * is what the domain this was found in is made of — and two values of different types are never
     * equal however much the numbers inside them agree.
     *
     * @param site where the comparison's own value is recorded, for a rule that meeting takes more
     *             than writing the two values. Empty where writing them is the whole of it, which is
     *             a clause: what it states is a relation, and the input the relation changes at is a
     *             pair of counts that are equal
     */
    private static Met metBetween(BoundaryTarget.EqualTerms line, BehaviorInputs where,
                                  List<RowOutcome> rows,
                                  java.util.function.BiPredicate<Place, Place> holds,
                                  java.util.OptionalInt site) {
        boolean unreadable = false;
        for (RowOutcome row : rows) {
            NumericTerm.Reading on = line.on()
                    .read(where.valueAt(row, line.on().path()), line.carrier());
            NumericTerm.Reading against = line.against()
                    .read(where.valueAt(row, line.against().path()), line.carrier());
            if (on instanceof NumericTerm.Reading.Missing
                    || against instanceof NumericTerm.Reading.Missing) {
                unreadable = true;
                continue;
            }
            if (on instanceof NumericTerm.Reading.Number here
                    && against instanceof NumericTerm.Reading.Number there
                    && holds.test(here.value(), there.value())
                    && site.stream().allMatch(litBy(row)::contains)) {
                return Met.YES;
            }
        }
        return unreadable ? Met.UNREADABLE : Met.NO;
    }

    /** What a reading of the rows comes to, once what could not be read is accounted for. */
    private static ItemAssessment.Coverage verdictOf(
            Met met, boolean guard, souther.compiler.query.Adequacy.Observed observed) {
        List<RowOutcome> rows = observed.rows();
        if (met == Met.YES) {
            return new ItemAssessment.Coverage.Hit();
        }
        if (met == Met.UNREADABLE) {
            return new ItemAssessment.Coverage.Undecided();
        }
        // A row nothing read may be the row that is at this value. Found is still found — one row at
        // the boundary settles it whatever else went unread — but not-found is not settled.
        if (observed.someRowsUnseen()) {
            return new ItemAssessment.Coverage.Undecided();
        }
        // Nor is a hit that could not be looked for: a row that never finished left no hits, and a
        // guard's line is met by going through the comparison.
        if (guard && rows.stream().anyMatch(
                row -> row.disposition() == souther.compiler.observe.Disposition.INCOMPLETE)) {
            return new ItemAssessment.Coverage.Undecided();
        }
        return new ItemAssessment.Coverage.Missed();
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
    private static ItemAssessment.Writability writabilityOf(
            ItemAssessment.Coverage coverage, boolean knownWritable,
            ItemAssessment.Attempt attempt) {
        if (coverage instanceof ItemAssessment.Coverage.Hit) {
            return new ItemAssessment.Writability.WitnessedByRow();
        }
        if (attempt instanceof ItemAssessment.Attempt.Built) {
            return new ItemAssessment.Writability.WitnessedByConstruction();
        }
        // A refusal and an attempt nobody made leave the same verdict, and a projection that read
        // every rule proves what neither of them found. Which is where the asymmetry lives: nothing
        // a search does can take a proof away, because nothing a search does is evidence against.
        return knownWritable ? new ItemAssessment.Writability.ProvenByProjection()
                : new ItemAssessment.Writability.Unknown();
    }

    /**
     * Whether a candidate is worth building for this boundary.
     *
     * <p>A line nothing measured is not a line an author is behind on. Where the arms were not asked
     * for, a guard's line has no answer at all, and where a row went unread the row that is at this
     * value may be one of the rows nothing saw — building a candidate for either hands somebody a
     * specific piece of work that may already be done.
     */
    private static boolean worthBuilding(ItemAssessment.Coverage coverage) {
        return coverage instanceof ItemAssessment.Coverage.Missed
                || (coverage instanceof ItemAssessment.Coverage.NotMeasured absent
                        && absent.reason() == ItemAssessment.Coverage.Reason.NO_ROWS);
    }

    /**
     * The first gate a {@code guard}'s line did not get through.
     *
     * <p>Its own path, because a guard's line and an invariant's are not measured the same way and so
     * cannot fail to be measured for the same reasons. Meeting this one takes the comparison having
     * run, which puts the arms in front of the rows: nothing a row carries decides it until the
     * classes that record where the row went exist and survived.
     */
    private static ItemAssessment.Coverage.Reason whyNoGuardLine(
            List<RowOutcome> rows, boolean armsAsked, boolean armsUnseen, boolean someRowsUnseen) {
        if (!armsAsked) {
            return ItemAssessment.Coverage.Reason.ARMS_NOT_ASKED;
        }
        if (armsUnseen) {
            return ItemAssessment.Coverage.Reason.ARMS_UNREADABLE;
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
    private static ItemAssessment.Coverage.Reason whyNoInvariantLine(
            List<RowOutcome> rows, boolean someRowsUnseen) {
        // Nothing read is not the same as nothing written. A source that could not be evaluated may
        // hold the row that is at this line, so the question is undecided rather than unasked, and
        // the reading below settles it that way.
        return rows.isEmpty() && !someRowsUnseen
                ? ItemAssessment.Coverage.Reason.NO_ROWS : null;
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
    private static Met metAt(Axis axis, BehaviorInputs where, List<RowOutcome> rows,
                             java.util.function.Predicate<Place> holds,
                             java.util.OptionalInt site) {
        boolean unreadable = false;
        for (RowOutcome row : rows) {
            switch (readingFor(axis, where, row)) {
                case NumericTerm.Reading.Missing _ -> unreadable = true;
                case NumericTerm.Reading.NotNumber _ -> { }
                case NumericTerm.Reading.Number number -> {
                    if (holds.test(number.value()) && site.stream().allMatch(litBy(row)::contains)) {
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
    private static NumericTerm.Reading readingFor(Axis axis, BehaviorInputs where, RowOutcome row) {
        return axis.term().read(where.valueAt(row, axis.path()),
                axis.term().carrierAt(axis.type(), where.symbols()));
    }

    private Coverages() {}

    /**
     * The sites a row is known to have gone through.
     *
     * <p>Read as a {@code switch} so that a counting this does not know about is a compile error
     * here rather than a row silently counted as having lit nothing. A row whose counting was never
     * read lights none that anything here can name, and that it was left undecided is said where the
     * row is reported.
     */
    private static java.util.Set<Integer> litBy(RowOutcome row) {
        return switch (row.run().counting()) {
            case Counting.Read read -> read.hits();
            case Counting.Unread _ -> java.util.Set.of();
        };
    }

}
